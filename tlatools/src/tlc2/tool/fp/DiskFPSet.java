// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import java.io.EOFException;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.net.InetAddress;
import java.rmi.RemoteException;
import java.text.DecimalFormat;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.LongAdder;
import java.util.logging.Logger;

import javax.management.NotCompliantMBeanException;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCTrace;
import tlc2.tool.TLCTrace.Enumerator;
import tlc2.tool.fp.management.DiskFPSetMXWrapper;
import tlc2.tool.management.TLCStandardMBean;
import tlc2.util.BufferedRandomAccessFile;
import tlc2.util.IdThread;
import util.Assert;
import util.FileUtil;


/**
 * A <code>DiskFPSet</code> is a subtype of <code>FPSet</code> that uses a
 * bounded amount of memory. Any fingerprints that don't fit in memory are
 * written to backing disk files. As required by the <code>FPSet</code> class,
 * this class's methods are thread-safe.
 * <p>
 * This implementation uses a single sorted disk file on which interpolated
 * binary search is performed. It keeps a separate
 * <TT>BufferedRandomAccessFile</TT> object open on the disk file per worker
 * thread. Hence, a new <TT>BufferedRandomAccessFile</TT> object does not have
 * to be created and destroyed on each <TT>contains</TT> operation. Multiple
 * disk seeks and reads may be required on each lookup, but in practice, the
 * numbers are very close to one (we have measured 1.05 seek operations and 1.1
 * read operations per lookup).
 * <p>
 * The implementation uses smart synchronization (using the
 * <code>ReadersWriterLock</code> class) so lookups on disk can be performed in
 * parallel.
 * <p>
 * We use the MSB of a fingerprint to indicate if it has been flushed to disk.
 * By doing so, we lose one bit of the fingerprint. However, we will get this
 * bit back if using MultiFPSet.
 */
// TODO-MAK Overlap flushTable-to-disk with reads
// TODO-MAK Flush asynchronously and with multiple threads (Exploit SSD support
// for multiple concurrent readers)
@SuppressWarnings("serial")
public abstract class DiskFPSet extends FPSet implements FPSetStatistic {

	protected final static Logger LOGGER = Logger.getLogger(DiskFPSet.class.getName());

	protected static final long MARK_FLUSHED = 0x8000000000000000L;
	protected static final long FLUSHED_MASK = 0x7FFFFFFFFFFFFFFFL;
	
	// fields
	/**
	 * upper bound on "tblCnt"
	 */
	protected long maxTblCnt;

	/**
	 * directory name for metadata
	 */
	protected String metadir;
	/**
	 * name of backing file
	 */
	protected String fpFilename;
	protected String tmpFilename;
	/**
	 * Number of entries on disk. This is equivalent to the current number of fingerprints stored on disk.
	 * @see DiskFPSet#getFileCnt()
	 */
	protected long fileCnt;
	/**
	 * Has a flusher thread been selected? 
	 * 
	 * This is necessary because multiple threads can be in the second synchronized block 
	 * of the put(long) method. The first one is waiting to become the writer at rwLock.BeginWrite(),
	 * a second has the this.rwLock monitor and possibly inserts a second fp into memory.
	 */
	protected AtomicBoolean flusherChosen;
	/**
	 * number of entries in "tbl". This is equivalent to the current number of fingerprints stored in in-memory cache/index.
	 * @see DiskFPSet#getTblCnt()
	 */
	protected LongAdder tblCnt; 
	// http://concurrencyfreaks.blogspot.de/2013/09/longadder-is-not-sequentially-consistent.html
	/**
	 * Number of used slots in tbl by a bucket
	 * @see DiskFPSet#getTblLoad()
	 */
	protected LongAdder tblLoad;
	
	/**
	 * Number of allocated bucket slots across the complete index table. tblCnt will always <= bucketCnt;
	 * @see DiskFPSet#getBucketCapacity()
	 */
	protected long bucketsCapacity;
	
	/**
	 * one per worker thread
	 */
	protected BufferedRandomAccessFile[] braf;
	/**
	 * a pool of available brafs
	 */
	protected BufferedRandomAccessFile[] brafPool;
	protected int poolIndex;

	/**
	 * index of first fp on each disk page
	 * special case: last entry is last fp in file
	 * if <code>null</code>, no disk file exists yet
	 */
	protected long[] index;
	
	// statistics
	protected LongAdder memHitCnt = new LongAdder();
	protected LongAdder diskHitCnt = new LongAdder();
	private LongAdder diskLookupCnt = new LongAdder();
	protected LongAdder diskWriteCnt = new LongAdder();
	private LongAdder diskSeekCnt = new LongAdder();
	private LongAdder diskSeekCache = new LongAdder();
	
	// indicate how many cp or disk grow in put(long) has occurred
	private int checkPointMark;
	protected int growDiskMark;

	/**
	 * The load factor and initial capacity for the hashtable.
	 */
	protected static final int LogMaxLoad = 4;
	static final int InitialBucketCapacity = (1 << LogMaxLoad);

	/* Number of fingerprints per braf buffer. */
	public static final int NumEntriesPerPage = 8192 / (int) LongSize;
	
	/**
	 * This is (assumed to be) the auxiliary storage for a fingerprint that need
	 * to be respected to not cause an OOM.
	 * @see DiskFPSet#flushTable()
	 * @see DiskFPSet#index
	 */
	protected double getAuxiliaryStorageRequirement() {
		return 1.0d;
	}
	
	protected TLCStandardMBean diskFPSetMXWrapper;
	
	/**
	 * Accumulated wall clock time it has taken to flush this {@link FPSet} to
	 * disk
	 */
	protected long flushTime = 0L;
	
	/**
	 * 
	 */
	protected Flusher flusher;

	/**
	 * JMX force flush
	 */
	protected volatile boolean forceFlush = false;

	/**
	 * Construct a new <code>DiskFPSet2</code> object whose internal memory
	 * buffer of new fingerprints can contain up to
	 * <code>DefaultMaxTblCnt</code> entries. When the buffer fills up, its
	 * entries are atomically flushed to the FPSet's backing disk file.
	 * 
	 * @throws RemoteException
	 */
	protected DiskFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
		super(fpSetConfig);
		
		this.maxTblCnt = fpSetConfig.getMemoryInFingerprintCnt();
		if (maxTblCnt <= 0) {
			throw new IllegalArgumentException("Negative or zero upper storage limit");
		}
		this.fileCnt = 0;
		this.tblCnt = new LongAdder();
		this.tblLoad = new LongAdder();
		this.flusherChosen = new AtomicBoolean(false);
		this.index = null;
		
		try {
			diskFPSetMXWrapper = new DiskFPSetMXWrapper(this);
		} catch (NotCompliantMBeanException e) {
			// not expected to happen
			// would cause JMX to be broken, hence just log and continue
			MP.printWarning(
					EC.GENERAL,
					"Failed to create MBean wrapper for DiskFPSet. No statistics/metrics will be avaiable.",
					e);
			diskFPSetMXWrapper = TLCStandardMBean.getNullTLCStandardMBean();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#init(int, java.lang.String, java.lang.String)
	 */
	public FPSet init(int numThreads, String aMetadir, String filename)
			throws IOException {
		
		// Make it possible to pass in alternative location for the .fp and
		// .fp.tmp files. Per default they end up in the same location with the
		// trace and disk based state queue. This is sub-optimal if node has > 1
		// disk.
		// This has to be an absolute path. 
		final String propMetaDirPrefix = System.getProperty(DiskFPSet.class.getName() + ".metadirPrefix");
		if (propMetaDirPrefix == null) {
			this.metadir = aMetadir;
		} else {
			// If aMetadir is an absolute path name, we strip off the last part and append it to the prefix.
			File file = new File(aMetadir);
			if (file.isAbsolute()) {
				aMetadir = file.getName();
			}
			final String folder = propMetaDirPrefix + File.separator
					+ aMetadir;
			new File(folder).mkdirs();
			this.metadir = folder;
		}
		
		// set the filename
		// concat here to not do it every time in mergeEntries 
		filename = metadir + FileUtil.separator + filename;
		this.tmpFilename = filename + ".tmp";
		this.fpFilename = filename + ".fp";
		
		// allocate array of BufferedRAF objects (+1 for main thread)
		this.braf = new BufferedRandomAccessFile[numThreads];
		this.brafPool = new BufferedRandomAccessFile[5];
		this.poolIndex = 0;

		
		try {
			// create/truncate backing file:
			FileOutputStream f = new FileOutputStream(this.fpFilename);
			f.close();

			// open all "this.braf" and "this.brafPool" objects on currName:
			for (int i = 0; i < numThreads; i++) {
				this.braf[i] = new BufferedRandomAccessFile(
						this.fpFilename, "r");
			}
			for (int i = 0; i < brafPool.length; i++) {
				this.brafPool[i] = new BufferedRandomAccessFile(
						this.fpFilename, "r");
			}
		} catch (IOException e) {
			// fatal error -- print error message and exit
			String message = MP.getMessage(EC.SYSTEM_UNABLE_TO_OPEN_FILE,
					new String[] { this.fpFilename, e.getMessage() });
			throw new IOException(message);
		}
		return this;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#size()
	 */
	public long size() {
		return this.getTblCnt() + this.fileCnt;
	}

	public abstract long sizeof();

	/* (non-Javadoc)
	 * @see java.lang.Object#finalize()
	 */
	public final void finalize() {
		/* Close any backing disk files in use by this object. */
		for (int i = 0; i < this.braf.length; i++) {
			try {
				this.braf[i].close();
			} catch (IOException e) { /* SKIP */
			}
		}
		for (int i = 0; i < this.brafPool.length; i++) {
			try {
				this.brafPool[i].close();
			} catch (IOException e) { /* SKIP */
			}
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#addThread()
	 */
	public final void addThread() throws IOException {
		synchronized (this.braf) {
			int len = this.braf.length;
			BufferedRandomAccessFile[] nraf = new BufferedRandomAccessFile[len + 1];
			for (int i = 0; i < len; i++) {
				nraf[i] = this.braf[i];
			}
			nraf[len] = new BufferedRandomAccessFile(this.fpFilename, "r");
			this.braf = nraf;
		}
	}

	/**
	 * @return true iff the current in-memory buffer has to be flushed to disk
	 *         to make room.
	 */
	protected boolean needsDiskFlush() {
		//TODO does not take the bucket load factor into account?
		// Buckets can grow beyond VM heap size if:
		// A) the FP distribution causes the index tbl to be unevenly populated.
		// B) the FP distribution reassembles linear fill-up/down which 
		// causes tblCnt * buckets with initial load factor to be allocated.
		return (this.getTblCnt() >= this.maxTblCnt) || forceFlush ;
	}

	/**
	 * Checks if the given fingerprint has a value that can be correctly stored
	 * by this FPSet
	 * 
	 * @param fp The fingerprint to check validity for.
	 * @return An alternative fingerprint value to map the invalid to.
	 */
	protected long checkValid(long fp) {
		if (fp == 0L) {
			//TODO Decide on strategy:
			// - Throw exception
			// - Raise warning (a 0L fp causes all subsequent states to be
			// explored twice, unless cycle)
			// - Map to a unused fp value
			// - use a dedicated boolean class member to hold 0L
		}
		return fp;
	}

	/**
	 * @param fp The fingerprint to lookup in memory
	 * @return true iff "fp" is in the hash table. 
	 */
	abstract boolean memLookup(long fp);

	/**
	 * Return "true" if "fp" is contained in the hash table; otherwise, insert
	 * it and return "false". Precondition: msb(fp) = 0
	 * @throws IOException 
	 */
	abstract boolean memInsert(long fp) throws IOException;

	/**
	 * Locks and unlocks tbl
	 */
	abstract void acquireTblWriteLock();
	abstract void releaseTblWriteLock();
	
	/**
	 * Look on disk for the fingerprint "fp". This method requires that
	 * "this.rwLock" has been acquired for reading by the caller.
	 * @param fp The fingerprint to lookup on disk
	 * @return true iff fp is on disk
	 */
	final boolean diskLookup(long fp) throws IOException {
		if (this.index == null) {
			return false;
		}
		
		// Increment disk lookup counter
		this.diskLookupCnt.increment();
		
		// search in index for position to seek to
		// do interpolated binary search
		final int indexLength = this.index.length;
		int loPage = 0, hiPage = indexLength - 1;
		long loVal = this.index[loPage];
		long hiVal = this.index[hiPage];

		// Test boundary cases (if not inside interval)
		if (fp < loVal || fp > hiVal) {
			return false;
		}
		if (fp == hiVal) {// why not check loVal? memLookup would have found it already!	
			return true;
		}
		final double dfp = (double) fp;

		// a) find disk page that would potentially contain the fp. this.index contains 
		// the first fp of each disk page
		while (loPage < hiPage - 1) {
			/*
			 * Invariant: If "fp" exists in the file, the (zero-based) page
			 * number within the file on which it occurs is in the half-open
			 * interval "[loPage, hiPage)".
			 * 
			 * loVal <= fp < hiVal exists x: loPage < x < hiPage
			 */
			final double dhi = (double) hiPage;
			final double dlo = (double) loPage;
			final double dhiVal = (double) hiVal;
			final double dloVal = (double) loVal;
			
			int midPage = (loPage + 1)
					+ (int) ((dhi - dlo - 1.0) * (dfp - dloVal) / (dhiVal - dloVal));
			if (midPage == hiPage)
				midPage--; // Needed due to limited precision of doubles

			Assert.check(loPage < midPage && midPage < hiPage,
					EC.SYSTEM_INDEX_ERROR);
			final long v = this.index[midPage];
			if (fp < v) {
				hiPage = midPage;
				hiVal = v;
			} else if (fp > v) {
				loPage = midPage;
				loVal = v;
			} else {
				// given fp happens to be in index file
				return true;
			}
		}
		return diskLookupBinarySearch(fp, indexLength, loPage, hiPage, loVal, hiVal, dfp);
	}

	private final boolean diskLookupBinarySearch(final long fp, final int indexLength, final int loPage, final int hiPage, long loVal, long hiVal,
			final double dfp) throws IOException {
		// no page is in between loPage and hiPage at this point
		Assert.check(hiPage == loPage + 1, EC.SYSTEM_INDEX_ERROR);

		boolean diskHit = false;
		long midEntry = -1L;
		// lower bound for the interval search in 
		long loEntry = ((long) loPage) * NumEntriesPerPage;
		// upper bound for the interval search in 
		long hiEntry = ((loPage == indexLength - 2) ? this.fileCnt - 1
				: ((long) hiPage) * NumEntriesPerPage);
		try {
			// b0) open file for reading that is associated with current thread
			BufferedRandomAccessFile raf;
			final int id = IdThread.GetId(this.braf.length);
			if (id < this.braf.length) {
				raf = this.braf[id];
			} else {
				raf = poolOpen();
			}
			
			// b1) do interpolated binary search on disk page determined by a)

			while (loEntry < hiEntry) {
				/*
				 * Invariant: If "fp" exists in the file, its (zero-based)
				 * position within the file is in the half-open interval
				 * "[loEntry, hiEntry)".
				 */
				midEntry = calculateMidEntry(loVal, hiVal, dfp, loEntry, hiEntry);

				Assert.check(loEntry <= midEntry && midEntry < hiEntry,
						EC.SYSTEM_INDEX_ERROR);
				// midEntry calculation done on logical indices,
				// addressing done on bytes, thus convert to long-addressing (* LongSize)
				if (raf.seeek(midEntry * LongSize)) {
					diskSeekCnt.increment();
				} else {
					diskSeekCache.increment();
				}
				final long v = raf.readLong();

				if (fp < v) {
					hiEntry = midEntry;
					hiVal = v;
				} else if (fp > v) {
					loEntry = midEntry + 1;
					loVal = v;
				} else {
					diskHit = true;
					break;
				}
			}
			// b2) done doing disk search -> close file (finally candidate? => not really because if we exit with error, TLC exits)
			if (id >= this.braf.length) {
				poolClose(raf);
			}
		} catch (final IOException e) {
			if(midEntry * LongSize < 0) {
			 // LL modified error message on 7 April 2012
				MP.printError(EC.GENERAL, new String[]{"looking up a fingerprint, and" + 
			            "\nmidEntry turned negative (loEntry, midEntry, hiEntry, loVal, hiVal): ",
						Long.toString(loEntry) +" ", Long.toString(midEntry) +" ", Long.toString(hiEntry) +" ", Long.toString(loVal) +" ", Long.toString(hiVal)}, e);
			}
			MP.printError(EC.SYSTEM_DISKGRAPH_ACCESS, e);
			throw e;
		}
		return diskHit;
	}

	private final BufferedRandomAccessFile poolOpen() throws IOException {
		synchronized (this.brafPool) {
			if (this.poolIndex < this.brafPool.length) {
				return this.brafPool[this.poolIndex++];
			} else {
				return new BufferedRandomAccessFile(
						this.fpFilename, "r");
			}
		}
	}

	private final void poolClose(final BufferedRandomAccessFile raf) throws IOException {
		synchronized (this.brafPool) {
			if (this.poolIndex > 0) {
				this.brafPool[--this.poolIndex] = raf;
			} else {
				raf.close();
			}
		}
	}

	/**
	 * Calculates a mid entry where to divide the interval
	 * 
	 * @param loVal Smallest fingerprint in this interval {@link Long#MIN_VALUE} to {@link Long#MAX_VALUE}
	 * @param hiVal Biggest fingerprint in this interval {@link Long#MIN_VALUE} to {@link Long#MAX_VALUE}
	 * @param fp The fingerprint we are searching for {@link Long#MIN_VALUE} to {@link Long#MAX_VALUE}
	 * @param loEntry low position/bound index  0 to {@link Long#MAX_VALUE}
	 * @param hiEntry high position/bound index loEntry to {@link Long#MAX_VALUE}
	 * 
	 * @return A mid entry where to divide the interval
	 */
	long calculateMidEntry(long loVal, long hiVal, final double dfp, long loEntry, long hiEntry) {

		final double dhi = (double) hiEntry;
		final double dlo = (double) loEntry;
		final double dhiVal = (double) hiVal;
		final double dloVal = (double) loVal;
		
		long midEntry = loEntry
				+ (long) ((dhi - dlo) * (dfp - dloVal) / (dhiVal - dloVal));
		
		if (midEntry == hiEntry) {
			midEntry--;
		}

		return midEntry;
	}

	protected int currIndex;
	protected int counter;

	protected final void writeFP(RandomAccessFile outRAF, long fp)
			throws IOException {
		outRAF.writeLong(fp);
		diskWriteCnt.increment();
		// update in-memory index file
		if (this.counter == 0) {
			this.index[this.currIndex++] = fp;
			this.counter = NumEntriesPerPage;
		}
		this.counter--;
	}

	/**
	 * @param buffLen The current {@link DiskFPSet#tbl} length
	 * @return The new required length for the {@link DiskFPSet#index}
	 */
	protected int calculateIndexLen(final long buffLen) {
		// +2L because we always need the lo and hi bounds for the index.
		long indexLen = ((this.fileCnt + buffLen - 1L) / (long) NumEntriesPerPage) + 2L;

		//TODO this can cause a NegativeArraySizeException if fileCnt becomes sufficiently large
		Assert.check(indexLen > 0, EC.GENERAL);
		
		return (int) indexLen;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#close()
	 */
	public final void close() {
		// close JMX stats
		diskFPSetMXWrapper.unregister();
		
		for (int i = 0; i < this.braf.length; i++) {
			try {
				this.braf[i].close();
			} catch (IOException e) { /* SKIP */
			}
		}
		for (int i = 0; i < this.brafPool.length; i++) {
			try {
				this.brafPool[i].close();
			} catch (IOException e) { /* SKIP */
			}
		}
		this.poolIndex = 0;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#exit(boolean)
	 */
	public void exit(boolean cleanup) throws IOException {
		super.exit(cleanup);
		if (cleanup) {
			// Delete the metadata directory:
			FileUtil.deleteDir(this.metadir, true);
		}
		String hostname = InetAddress.getLocalHost().getHostName();
		MP.printMessage(EC.TLC_FP_COMPLETED, hostname);

		System.exit(0);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#checkFPs()
	 */
	public long checkFPs() throws IOException {
		// It seems pointless to acquire the locks when checkFPs is only
		// executed after model checking has finished. Lock the disk
		// fingerprint sets though. Acquiring the locks is cheap.
		acquireTblWriteLock();
		flusher.flushTable();
		releaseTblWriteLock();

		RandomAccessFile braf = new BufferedRandomAccessFile(
				this.fpFilename, "r");
		long fileLen = braf.length();
		long dis = Long.MAX_VALUE;
		if (fileLen > 0) {
			long x = braf.readLong();
			while (braf.getFilePointer() < fileLen) {
				long y = braf.readLong();
				long dis1 = y - x;
				if (dis1 >= 0) {
					dis = Math.min(dis, dis1);
				}
				x = y;
			}
		}
		braf.close();
		return dis;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#beginChkpt(java.lang.String)
	 */
	public void beginChkpt(String fname) throws IOException {
		
		this.flusherChosen.set(true);
		acquireTblWriteLock();
		
		flusher.flushTable();
		FileUtil.copyFile(this.fpFilename,
				this.getChkptName(fname, "tmp"));
		checkPointMark++;

		releaseTblWriteLock();
		this.flusherChosen.set(false);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#commitChkpt(java.lang.String)
	 */
	public void commitChkpt(String fname) throws IOException {
		File oldChkpt = new File(this.getChkptName(fname, "chkpt"));
		File newChkpt = new File(this.getChkptName(fname, "tmp"));
		if (!newChkpt.renameTo(oldChkpt)) {
			throw new IOException("DiskFPSet.commitChkpt: cannot delete "
					+ oldChkpt);
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#recover(java.lang.String)
	 */
	public void recover(String fname) throws IOException {
		RandomAccessFile chkptRAF = new BufferedRandomAccessFile(
				this.getChkptName(fname, "chkpt"), "r");
		RandomAccessFile currRAF = new BufferedRandomAccessFile(
				this.fpFilename, "rw");

		this.fileCnt = chkptRAF.length() / LongSize;
		int indexLen = (int) ((this.fileCnt - 1) / NumEntriesPerPage) + 2;
		this.index = new long[indexLen];
		this.currIndex = 0;
		this.counter = 0;

		long fp = 0L;
		try {
			long predecessor = Long.MIN_VALUE;
			while (true) {
				fp = chkptRAF.readLong();
				this.writeFP(currRAF, fp);
				// check invariant
				Assert.check(predecessor < fp, EC.SYSTEM_INDEX_ERROR);
				predecessor = fp;
			}
		} catch (EOFException e) {
			Assert.check(this.currIndex == indexLen - 1, EC.SYSTEM_INDEX_ERROR);
			this.index[indexLen - 1] = fp;
		}

		chkptRAF.close();
		currRAF.close();

		// reopen a BufferedRAF for each thread
		for (int i = 0; i < this.braf.length; i++) {
			// Better way would be to provide method BRAF.open
			// close and reopen
			this.braf[i].close();
			this.braf[i] = new BufferedRandomAccessFile(this.fpFilename,
					"r");
		}
		for (int i = 0; i < this.brafPool.length; i++) {
			// Better way would be to provide method BRAF.open
			// close and reopen
			this.brafPool[i].close();
			this.brafPool[i] = new BufferedRandomAccessFile(
					this.fpFilename, "r");
		}
		this.poolIndex = 0;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#beginChkpt()
	 */
	public final void beginChkpt() throws IOException {
		// @see tlc2.tool.fp.DiskFPSet.commitChkpt()
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#commitChkpt()
	 */
	public final void commitChkpt() throws IOException { 
		/* SKIP */
		// DiskFPSet checkpointing is a no-op, because DiskFPSet recreates 
		// the fingerprints from the TLCTrace file. Not from its own .fp file. 
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#recoverFP(long)
	 */
	public final void recoverFP(long fp) throws IOException {
		// This implementation used to group n fingerprints into a sorted
		// in-memory page. Pages were subsequently merged on-disk directly,
		// creating the on-disk storage file for DiskFPSets.
		//
		// The new algorithm simply "replays" the fingerprints found in the
		// trace file. It's biggest disadvantage is a performance penalty it
		// pays because it doesn't group fingerprints. On the other hand, it has
		// advantages over the old algorithm:
		// 
		// - Simplified logic/code
		// - No need for a long[] recovery buffer
		// - TLC runs with a warm in-memory fingerprint cache
		// - With large amounts of available fingerprint set memory, the .fp
		// file might actually never be written. This means that the FPSet never
		// has to go to disk during contains/put which yields a better overall
		// runtime performance.
		// 
		// TODO Use original on-disk merge if it is known that the fingerprints
		// won't fit into memory anyway.
		
		// The code below is put(long) stripped from synchronization and
		// statistics code to speed up recovery. Thus, recovery relys on
		// exclusive access to the fingerprint set, which it has during
		// recovery.
		long fp0 = fp & FLUSHED_MASK;
		boolean unique = !this.memInsert(fp0);
		Assert.check(unique, EC.SYSTEM_CHECKPOINT_RECOVERY_CORRUPT, "");
		if (needsDiskFlush()) {
			this.flusher.flushTable();
		}
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#recover()
	 */
	public final void recover(TLCTrace trace) throws IOException {
		final Enumerator elements = trace.elements();
		while (elements.nextPos() != -1) {
			long fp = elements.nextFP();
			this.recoverFP(fp);
		}
		elements.close();
	}

	private String getChkptName(String fname, String name) {
		return this.metadir + FileUtil.separator + fname + ".fp." + name;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#checkInvariant()
	 */
	public boolean checkInvariant() throws IOException {
		acquireTblWriteLock();
		flusher.flushTable(); // No need for any lock here
		final RandomAccessFile braf = new BufferedRandomAccessFile(
				this.fpFilename, "r");
		try {
			final long fileLen = braf.length();
			long predecessor = Long.MIN_VALUE;
			if (fileLen > 0) {
				while (braf.getFilePointer() < fileLen) {
					long l = braf.readLong();
					if (predecessor >= l) {
						return false;
					}
					predecessor = l;
				}
			}
		} finally {
			braf.close();
			releaseTblWriteLock();
		}
		return true;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#checkInvariant(long)
	 */
	public boolean checkInvariant(long expectedFPCnt) throws IOException {
		return checkInvariant() && size() == expectedFPCnt;
	}

	
	/**
	 * @return the bucketsCapacity counting all allocated (used and unused) fp slots in the in-memory storage.
	 */
	public long getBucketCapacity() {
		return bucketsCapacity;
	}
	
	/**
	 * @return The allocated (used and unused) array length of the first level in-memory storage.
	 */
	public long getTblCapacity() {
		return -1L;
	}

	/**
	 * @return the index.length
	 */
	public long getIndexCapacity() {
		if(index == null) {
			return 0;
		}
		return index.length;
	}

	/**
	 * @return {@link DiskFPSet#getBucketCapacity()} + {@link DiskFPSet#getTblCapacity()} + {@link DiskFPSet#getIndexCapacity()}.
	 */
	public long getOverallCapacity() {
		return getBucketCapacity() + getTblCapacity() + getIndexCapacity();
	}
	
	/**
	 * @return	Number of used slots in tbl by a bucket
	 * {@link DiskFPSet#getTblLoad()} <= {@link DiskFPSet#getTblCnt()}
	 */
	public long getTblLoad() {
		return tblLoad.sum();
	}
	
	/**
	 * @return the amount of fingerprints stored in memory. This is less or equal to {@link DiskFPSet#getTblCnt()} depending on if there collision buckets exist. 
	 */
	public long getTblCnt() {
		return tblCnt.sum();
	}
	
	/**
	 * @return the maximal amount of fingerprints stored in memory. 
	 */
	public long getMaxTblCnt() {
		return maxTblCnt;
	}
	
	/**
	 * @return the amount of fingerprints stored on disk
	 */
	public long getFileCnt() {
		return fileCnt;
	}
	
	/**
	 * @return the diskLookupCnt
	 */
	public long getDiskLookupCnt() {
		return diskLookupCnt.sum();
	}

	/**
	 * @return the diskHitCnt
	 */
	public long getMemHitCnt() {
		return memHitCnt.sum();
	}

	/**
	 * @return the diskHitCnt
	 */
	public long getDiskHitCnt() {
		return diskHitCnt.sum();
	}

	/**
	 * @return the diskWriteCnt
	 */
	public long getDiskWriteCnt() {
		return diskWriteCnt.sum();
	}

	/**
	 * @return the diskSeekCnt
	 */
	public long getDiskSeekCnt() {
		return diskSeekCnt.sum();
	}
	
	/**
	 * @return the diskSeekCache
	 */
	public long getDiskSeekCache() {
		return diskSeekCache.sum();
	}

	/**
	 * @return the growDiskMark
	 */
	public int getGrowDiskMark() {
		return growDiskMark;
	}
	
	/**
	 * @return the checkPointMark
	 */
	public int getCheckPointMark() {
		return checkPointMark;
	}
	
	/**
	 * @see DiskFPSet#flushTime
	 */
	public long getFlushTime() {
		return flushTime;
	}
	
	public void forceFlush() {
		forceFlush = true;
	}
	
	/**
	 * @return The (static) number of locks used to guard the set. 
	 */
	public int getLockCnt() {
		return 0;
	}
	
	/**
	 * @return The technical maximum of readers/writers this {@link DiskFPSet}
	 *         can handle. It doesn't show the actual numbers of active clients.
	 *         This value is equivalent to the amount of
	 *         {@link BufferedRandomAccessFile} instances.
	 */
	public int getReaderWriterCnt() {
		return this.braf.length + this.brafPool.length;
	}
	
	/**
	 * The load factor is a measure of how full the (primary) in-memory hash
	 * table is.
	 * 
	 * @return The primary in-memory table's current load factor in the domain
	 *         [0, 1]. If the {@link DiskFPSet} implementation doesn't support a
	 *         load factor, <code>-1d</code> is returned.
	 */
	public double getLoadFactor() {
		return ((double) this.getTblCnt()) / (double) this.maxTblCnt;
	}

	// /**
	// *
	// */
	// private final void mergeBuff(long[] buff, int len, File fpFile)
	// throws IOException {
	// File tmpFile = new File(this.filename + ".tmp");
	// tmpFile.delete();
	// BufferedRandomAccessFile fpRAF = new BufferedRandomAccessFile(fpFile,
	// "rw");
	// BufferedRandomAccessFile tmpRAF = new BufferedRandomAccessFile(tmpFile,
	// "rw");
	// int i = 0;
	// long value = 0L;
	// try {
	// value = fpRAF.readLong();
	// while (i < len) {
	// if (value < buff[i]) {
	// tmpRAF.writeLong(value);
	// value = fpRAF.readLong();
	// }
	// else {
	// tmpRAF.writeLong(buff[i++]);
	// }
	// }
	// } catch (EOFException e) { /*SKIP*/ }
	//
	// if (i < len) {
	// for (int j = i; j < len; j++) {
	// tmpRAF.writeLong(buff[j]);
	// }
	// }
	// else {
	// try {
	// do {
	// tmpRAF.writeLong(value);
	// value = fpRAF.readLong();
	// } while (true);
	// } catch (EOFException e) { /*SKIP*/ }
	// }
	//
	// fpRAF.close();
	// tmpRAF.close();
	// fpFile.delete();
	// tmpFile.renameTo(fpFile);
	// }

	public abstract class Flusher {
		
		protected void prepareTable() {
			// no-op
			// subclasses may override
		}

		/**
		 * Flush the contents of in-memory "this.tbl" to the backing disk file, and update
		 * "this.index". This method requires that "this.rwLock" has been acquired
		 * for writing by the caller, and that the mutex "this.rwLock" is also held.
		 */
		void flushTable() throws IOException {
			if (getTblCnt() == 0)
				return;
			
			prepareTable();
			
//			// reset statistic counters
//			this.memHitCnt = 0;
//
//			this.diskHitCnt = 0;
//			this.diskWriteCnt = 0;
//			this.diskSeekCnt = 0;
//			this.diskLookupCnt = 0;

			// merge array with disk file
			try {
				this.mergeNewEntries();
			} catch (IOException e) {
				String msg = "Error: merging entries into file "
						+ fpFilename + "  " + e;
				throw new IOException(msg);
			}

			tblCnt.reset();
			bucketsCapacity = 0;
			tblLoad.reset();
		}

		/**
		 * Merge the values in "buff" into this FPSet's backing disk file. The
		 * values in "buff" are required to be in sorted order, and the write lock
		 * associated with "this.rwLock" must be held, as must the mutex
		 * "this.rwLock" itself.
		 */
		protected void mergeNewEntries() throws IOException {
			// Implementation Note: Unfortunately, because the RandomAccessFile
			// class (and hence, the BufferedRandomAccessFile class) does not
			// provide a way to re-use an existing RandomAccessFile object on
			// a different file, this implementation must close all existing
			// files and re-allocate new BufferedRandomAccessFile objects.
			for (int i = 0; i < braf.length; i++) {
				// Seek readers to zero position.
				braf[i].seek(0L);
			}
			for (int i = 0; i < brafPool.length; i++) {
				brafPool[i].close();
			}

			// create temporary file
			File tmpFile = new File(tmpFilename);
			tmpFile.delete();
			RandomAccessFile tmpRAF = new BufferedRandomAccessFile(tmpFile, "rw");
			tmpRAF.setLength((getTblCnt() + fileCnt) * FPSet.LongSize);

			// merge
			mergeNewEntries(braf, tmpRAF);
			
			// clean up
			for (int i = 0; i < braf.length; i++) {
				// close existing files (except brafPool[0])
				braf[i].close();
			}
			tmpRAF.close();
			try {
				FileUtil.replaceFile(tmpFilename, fpFilename);
			} catch (IOException e) {
				Assert.fail(EC.SYSTEM_UNABLE_NOT_RENAME_FILE, e);
			}

			// reopen a BufferedRAF for each thread
			for (int i = 0; i < braf.length; i++) {
				// Better way would be to provide method BRAF.open
				braf[i] = new BufferedRandomAccessFile(fpFilename, "r");
			}
			for (int i = 0; i < brafPool.length; i++) {
				// Better way would be to provide method BRAF.open
				brafPool[i] = new BufferedRandomAccessFile(fpFilename, "r");
			}
			
			// Verify disk file is sorted.
			assert checkFile(braf[0], index, fileCnt);
			
			poolIndex = 0;
		}
		
		protected abstract void mergeNewEntries(BufferedRandomAccessFile[] inRAFs, RandomAccessFile outRAF) throws IOException;
		
	}
	
	private static boolean checkFile(BufferedRandomAccessFile braf, long[] index, long elements) throws IOException {
		final long fileLen = braf.length();
		if (fileLen / LongSize != elements) {
			return false;
		}
		final long ptr = braf.getFilePointer();
		long predecessor = Long.MIN_VALUE;
		if (fileLen > 0) {
			predecessor = braf.readLong();
			if (predecessor != index[0]) {
				return false;
			}
			while (braf.getFilePointer() < fileLen) {
				long l = braf.readLong();
				if (predecessor >= l) {
					return false;
				}
				predecessor = l;
			}
		}
		braf.seek(ptr);
		return predecessor == index[index.length - 1];
	}
	
	/*
	 * Helper to read a fingerprint file (.fp) front to end and check for inconsistencies.   
	 */
	
	@SuppressWarnings("resource")
	public static void main(String[] args) throws IOException {
		if (args.length == 1 && !args[0].equals("")) {

			final BufferedRandomAccessFile braf = new BufferedRandomAccessFile(new File(args[0]), "r");

			final long elements = braf.length() / FPSet.LongSize;
			final DecimalFormat df = new DecimalFormat("###,###.###");
			System.out.println(String.format("About to scan %s elements.", df.format(elements)));

			long elem = 0L;
			for (long i = 0; i < elements; i++) {
				final long l = braf.readLong();
				if (l < elem) {
					System.err.println(
							String.format("Inconsistent elements %s at pos %s < %s at pos %s.", elem, i - 1L, l, i));
				}
				elem = l;
				if (i > 0 && i % 100000000L == 0L) {
					System.out.println(String.format("Scanned %s elements.", df.format(i)));
				}
			}
		} else if (args.length == 2 && !args[0].equals("") && !args[1].equals("")) {
			final BufferedRandomAccessFile superset = new BufferedRandomAccessFile(new File(args[0]), "r");
			final BufferedRandomAccessFile subset = new BufferedRandomAccessFile(new File(args[1]), "r");

			final long elements = subset.length() / FPSet.LongSize;
			final long fileLen = superset.length();

			OUTER: for (long i = 0; i < elements; i++) {
				final long l = subset.readLong();
				while (superset.getFilePointer() < fileLen) {
					final long m = superset.readLong();
					if (l == m) {
						continue OUTER;
					} else if (m > l) {
						System.err
								.println(String.format("Inconsistent element in superset %s not in superset at pos %s.",
										m, superset.getFilePointer()));
					}
				}
				System.err.println(
						String.format("Element in subset %s not in superset at pos %s.", l, subset.getFilePointer()));
			}

			System.out.println("Finished scanning files.");
		} else {
			System.err.println("Usage: DiskFPSet file.fp OR superset.fp subset.fp");
			System.exit(1);
		}
	}
}
