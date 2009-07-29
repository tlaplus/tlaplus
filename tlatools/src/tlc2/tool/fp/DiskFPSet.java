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

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCTrace;
import tlc2.util.BufferedRandomAccessFile;
import tlc2.util.IdThread;
import tlc2.util.ReadersWriterLock;
import tlc2.util.Sort;
import util.Assert;
import util.FileUtil;

/**
 * A <code>DiskFPSet</code> is a subtype of <code>FPSet</code> that
 * uses a bounded amount of memory. Any fingerprints that don't fit in
 * memory are written to backing disk files. As required by the
 * <code>FPSet</code> class, this class's methods are thread-safe.
 * <p>
 * This implementation uses a single sorted disk file on which
 * interpolated binary search is performed. It keeps a separate
 * <TT>BufferedRandomAccessFile</TT> object open on the disk file per
 * worker thread. Hence, a new <TT>BufferedRandomAccessFile</TT>
 * object does not have to be created and destroyed on each
 * <TT>contains</TT> operation. Multiple disk seeks and reads may be
 * required on each lookup, but in practice, the numbers are very
 * close to one (we have measured 1.05 seek operations and 1.1 read
 * operations per lookup).
 * <p>
 * The implementation uses smart synchronization (using the
 * <code>ReadersWriterLock</code> class) so lookups on disk can be
 * performed in parallel.
 * <p>
 * We use the MSB of a fingerprint to indicate if it has been
 * flushed to disk. By doing so, we lose one bit of the fingerprint.
 * However, we will get this bit back if using MultiFPSet.
 */

public class DiskFPSet extends FPSet {
    // fields
    private final int maxTblCnt;      // upper bound on "tblCnt"
    private final int mask;           // mask for computing hash function
    private String metadir;           // directory name for metadata
    private String filename;          // name of backing file

    private final ReadersWriterLock rwLock; // protects following fields    
    private long fileCnt;             // number of entries on disk
    private boolean flusherChosen;    // has a flusher thread been selected?
    private long[][] tbl;             // in-memory buffer of new entries
    private int tblCnt;               // number of entries in "tbl"
    private BufferedRandomAccessFile[] braf;     // one per worker thread
    private BufferedRandomAccessFile[] brafPool; // a pool of available brafs
    private int poolIndex;
  
    private long[] index;             // index of first fp on each disk page
                                      // special case: last entry is last fp in file

    // private long diskLookupCnt = 0L;
    // private long hitCnt2 = 0L;        // hits on this.tbl
    // private long hitCnt3 = 0L;        // hits on disk

    /* Log (base 2) of default number of new entries allowed to
       accumulate in memory before those entries are flushed to
       disk. */
    private static final int LogDefaultMaxTblCnt = 19;

    /* The load factor and initial capacity for the hashtable. */
    private static final int LogMaxLoad = 4;
    private static final int BucketSizeIncrement = 4;

    // computed constants
    private static final int DefaultMaxTblCnt = (1 << LogDefaultMaxTblCnt);
    private static final int LongSize = 8;     // sizeof(long)

    /* Number of fingerprints per braf buffer. */
    private static final int NumEntriesPerPage = 8192 / LongSize;

    /**
     * Construct a new <code>DiskFPSet2</code> object whose internal memory
     * buffer of new fingerprints can contain up to <code>DefaultMaxTblCnt</code>
     * entries. When the buffer fills up, its entries are atomically
     * flushed to the FPSet's backing disk file.
     */
    public DiskFPSet(int maxMemCnt) throws RemoteException {
        this.rwLock = new ReadersWriterLock();
        this.fileCnt = 0;
        this.flusherChosen = false;

	if (maxMemCnt == -1) {
	  maxMemCnt = DefaultMaxTblCnt;
	}
        int logMaxMemCnt = 1;
        maxMemCnt--;
        while (maxMemCnt > 1) {
            maxMemCnt >>>= 1;
            logMaxMemCnt++;
        }

        int capacity = 1 << (logMaxMemCnt - LogMaxLoad);
        this.tbl = new long[capacity][];
        this.tblCnt = 0;
        this.maxTblCnt = (1 << logMaxMemCnt);
        this.mask = capacity - 1;
        this.index = null;
    }

    public final void init(int numThreads, String metadir, String filename)
    throws IOException 
    {
        this.metadir = metadir;
        // set the filename
        this.filename = metadir + FileUtil.separator + filename;
        // allocate array of BufferedRAF objects (+1 for main thread)
        this.braf = new BufferedRandomAccessFile[numThreads];
        this.brafPool = new BufferedRandomAccessFile[5];
        this.poolIndex = 0;

        try 
        {
            // create/truncate backing file:
            FileOutputStream f = new FileOutputStream(this.getFPFilename());
            f.close();

            // open all "this.braf" and "this.brafPool" objects on currName:
            for (int i = 0; i < numThreads; i++) 
            {
                this.braf[i] = new BufferedRandomAccessFile(this.getFPFilename(), "r");
            }
            for (int i = 0; i < brafPool.length; i++) 
            {
                this.brafPool[i] = new BufferedRandomAccessFile(this.getFPFilename(), "r");
            }
        }
        catch (IOException e) 
        {
            // fatal error -- print error message and exit
            String message = MP.getMessage(EC.SYSTEM_UNABLE_TO_OPEN_FILE, new String[]{this.getFPFilename(), e.getMessage()});
            throw new IOException(message, e);
        }
    }

    public final long size() {
        synchronized (this.rwLock) {
            return this.tblCnt + this.fileCnt;
        }
    }

    public final long sizeof() {
        synchronized (this.rwLock) {
            long size = 44; // approx size of this DiskFPSet object
            size += 16 + (this.tbl.length * 4); // for this.tbl
            for (int i = 0; i < this.tbl.length; i++) {
                if (this.tbl[i] != null) {
                    size += 16 + (this.tbl[i].length * LongSize);
                }
            }
            return size;
        }
    }

    /* Close any backing disk files in use by this object. */
    public final void finalize() {
        for (int i = 0; i < this.braf.length; i++) {
            try {
                this.braf[i].close();
            }
	    catch (IOException e) { /*SKIP*/ }
        }
	for (int i = 0; i < this.brafPool.length; i++) {
            try {
                this.brafPool[i].close();
            }
	    catch (IOException e) { /*SKIP*/ }
        }
    }

    public final void addThread() throws IOException {
      synchronized (this.rwLock) {
	this.rwLock.BeginWrite();

	int len = this.braf.length;
	BufferedRandomAccessFile[] nraf = new BufferedRandomAccessFile[len+1];
	for (int i = 0; i < len; i++) {
	  nraf[i] = this.braf[i];
	}
	nraf[len] = new BufferedRandomAccessFile(this.getFPFilename(), "r");
	this.braf = nraf;

	this.rwLock.EndWrite();
      }
    }
  
    public final boolean put(long fp) throws IOException {
      long fp0 = fp & 0x7FFFFFFFFFFFFFFFL;
      synchronized (this.rwLock) {
	// First, look in in-memory buffer
	if (this.memLookup(fp0)) {
	  // this.hitCnt2++;
	  return true;
	}

	// block if disk is being re-written
	this.rwLock.BeginRead();
	// this.diskLookupCnt++;
      }

      // next, look on disk
      boolean diskHit = this.diskLookup(fp0);

      // end read; add to memory buffer if necessary
      synchronized (this.rwLock) {
	this.rwLock.EndRead();
	
	// In event of disk hit, return
	if (diskHit) {
	  // this.hitCnt3++;
	  return true;
	}

	// if disk lookup failed, add to memory buffer
	if (this.memInsert(fp0)) {
	  // this.hitCnt2++;
	  return true;
	} 

	// test if buffer is full
	if (this.tblCnt >= this.maxTblCnt && !this.flusherChosen) {
	  // block until there are no more readers
	  this.flusherChosen = true;
	  this.rwLock.BeginWrite();

	  // flush memory entries to disk
	  this.flushTable();

	  // finish writing
	  this.rwLock.EndWrite();
	  this.flusherChosen = false;
	}
	return false;
      }
    }

    public final boolean contains(long fp) throws IOException {
      long fp0 = fp & 0x7FFFFFFFFFFFFFFFL;
      synchronized (this.rwLock) {
	// First, look in in-memory buffer
	if (this.memLookup(fp0)) { return true; }

	// block if disk is being re-written
	this.rwLock.BeginRead();
	// this.diskLookupCnt++;
      }

      // next, look on disk
      boolean diskHit = this.diskLookup(fp0);

      // end read; add to memory buffer if necessary
      synchronized (this.rwLock) {
	this.rwLock.EndRead();
      }
      return diskHit;	
    }

    /* Return true iff "fp" is in the hash table. */
    private final boolean memLookup(long fp) {
      int index = (int)(fp & this.mask);
      long[] bucket = this.tbl[index];
      if (bucket == null) return false;

      int bucketLen = bucket.length;
      for (int i = 0; i < bucketLen && bucket[i] != 0L; i++) {
	if (fp == (bucket[i] & 0x7FFFFFFFFFFFFFFFL)) return true;
      }
      return false;
    }

    /**
     * Return "true" if "fp" is contained in the hash table; otherwise, 
     * insert it and return "false".
     * Precondition: msb(fp) = 0
     */
    private final boolean memInsert(long fp) {
        int index = (int)(fp & this.mask);
        long[] bucket = this.tbl[index];
    	if (bucket == null) {
	  bucket = new long[(1 << LogMaxLoad)];
	  bucket[0] = fp;	  
	  this.tbl[index] = bucket;
    	}
	else {
	  // search for entry
	  int bucketLen = bucket.length;
	  int i = -1;
	  int j = 0;
	  for (; j < bucketLen && bucket[j] != 0L; j++) {
	    long fp1 = bucket[j];
	    if (fp == (fp1 & 0x7FFFFFFFFFFFFFFFL)) { return true; }
	    if (i == -1 && fp1 < 0) { i = j; }
	  }
	  if (i == -1) {
	    if (j == bucketLen) {
	      // bucket is full; grow the bucket by BucketSizeIncrement
	      long[] oldBucket = bucket;
	      bucket = new long[bucketLen + BucketSizeIncrement];
	      System.arraycopy(oldBucket, 0, bucket, 0, bucketLen);
	      this.tbl[index] = bucket;
	    }
	    bucket[j] = fp;
	  }
	  else {
	    if (j != bucketLen) {
	      bucket[j] = bucket[i];
	    }
	    bucket[i] = fp;	    
	  }
	}
    	this.tblCnt++;
    	return false;
    }

    /**
     * Look on disk for the fingerprint "fp". This method requires
     * that "this.rwLock" has been acquired for reading by the caller.
     */
    private final boolean diskLookup(long fp) throws IOException {
        if (this.index == null) return false;
        // search in index for position to seek to
        // do interpolated binary search
        int loPage = 0, hiPage = this.index.length - 1;
        long loVal = this.index[loPage];
        long hiVal = this.index[hiPage];

        // Test boundary cases
        if (fp < loVal || fp > hiVal) return false;
        if (fp == hiVal) return true;
        double dfp = (double)fp;

        while (loPage < hiPage - 1) {
            /* Invariant: If "fp" exists in the file, the (zero-based)
               page number within the file on which it occurs is in the 
               half-open interval "[loPage, hiPage)". 

               loVal <= fp < hiVal 
               exists x: loPage < x < hiPage
            */
            double dhi = (double)hiPage, dlo = (double)loPage;
            double dhiVal = (double)hiVal, dloVal = (double)loVal;
            int midPage = (loPage+1) + (int)((dhi-dlo-1.0) * (dfp-dloVal) / (dhiVal-dloVal));
            if (midPage == hiPage) midPage--; // Needed due to limited precision of doubles

            Assert.check(loPage < midPage && midPage < hiPage, EC.SYSTEM_INDEX_ERROR);
            long v = this.index[midPage];
            if (fp < v) {
                hiPage = midPage; hiVal = v;
            }
	    else if (fp > v) {
                loPage = midPage; loVal = v;
            }
	    else {
                return true;
            }
        }
        Assert.check(hiPage == loPage + 1, EC.SYSTEM_INDEX_ERROR);

	boolean diskHit = false;
        try {
            // open file for reading
	    BufferedRandomAccessFile raf;
	    int id = IdThread.GetId(this.braf.length);
	    if (id < this.braf.length) {
	      raf = this.braf[id];
	    }
	    else {
	      synchronized(this.brafPool) {
		if (this.poolIndex < this.brafPool.length) {
		  raf = this.brafPool[this.poolIndex++];
		}
		else {
		  raf = new BufferedRandomAccessFile(this.getFPFilename(), "r");
		}
	      }
	    }
            // do interpolated binary search
            long loEntry = loPage * NumEntriesPerPage;
            long hiEntry = ((loPage == this.index.length - 2)
			    ? this.fileCnt - 1
			    : hiPage * NumEntriesPerPage);
            while (loEntry < hiEntry) {
                /* Invariant: If "fp" exists in the file, its (zero-based)
                   position within the file is in the half-open interval
                   "[loEntry, hiEntry)". */
                double dhi = (double)hiEntry, dlo = (double)loEntry;
                double dhiVal = (double)hiVal, dloVal = (double)loVal;
                long midEntry = loEntry + (long)((dhi - dlo) * (dfp - dloVal) / (dhiVal - dloVal));
                if (midEntry == hiEntry) midEntry--;
                
                Assert.check(loEntry <= midEntry && midEntry < hiEntry, EC.SYSTEM_INDEX_ERROR);
                raf.seek(midEntry * LongSize);
                long v = raf.readLong();

                if (fp < v) {
                    hiEntry = midEntry; hiVal = v;
                }
		else if (fp > v) {
                    loEntry = midEntry + 1; loVal = v;
                }
		else {
		    diskHit = true;
                    break;
                }
            }
	    if (id >= this.braf.length) {
	      synchronized(this.brafPool) {
		if (this.poolIndex > 0) {
		  this.brafPool[--this.poolIndex] = raf;
		}
		else {
		  raf.close();
		}
	      }
	    }
	}
	catch (IOException e) {
	  String msg = "Error: accessing file " + this.getFPFilename() + "  " + e;
	  throw new IOException(msg);
        }            
        return diskHit;
    }

    /**
     * Flush the contents of "this.tbl" to the backing disk file, and
     * update "this.index". This method requires that "this.rwLock"
     * has been acquired for writing by the caller, and that the mutex
     * "this.rwLock" is also held.
     */
    private final void flushTable() throws IOException {
        if (this.tblCnt == 0) return;

        // copy table contents into an array; erase table
        long[] buff = new long[this.tblCnt];
        int idx = 0;
        for (int j = 0; j < this.tbl.length; j++) {
	  long[] bucket = this.tbl[j];
	  if (bucket != null) {
	    int blen = bucket.length;
	    for (int k = 0; k < blen && bucket[k] > 0; k++) {
	      buff[idx++] = bucket[k];
	      bucket[k] |= 0x8000000000000000L;
	    }
	  }
        }
        this.tblCnt = 0;

        // sort in-memory entries
        Sort.LongArray(buff, buff.length);

        // merge array with disk file
        try {          
            this.mergeNewEntries(buff);
        }
	catch (IOException e) {
	  String msg = "Error: merging entries into file " + this.getFPFilename() + "  " + e;
	  throw new IOException(msg);
        }
    }
    
    /**
     * Merge the values in "buff" into this FPSet's backing disk file.
     * The values in "buff" are required to be in sorted order, and the
     * write lock associated with "this.rwLock" must be held, as must
     * the mutex "this.rwLock" itself.
     */
    private final void mergeNewEntries(long[] buff) throws IOException {
        // Implementation Note: Unfortunately, because the RandomAccessFile
        // class (and hence, the BufferedRandomAccessFile class) does not
        // provide a way to re-use an existing RandomAccessFile object on
        // a different file, this implementation must close all existing
        // files and re-allocate new BufferedRandomAccessFile objects.

        // close existing files (except brafPool[0])
        for (int i = 0; i < this.braf.length; i++) {
            this.braf[i].close();
        }
        for (int i = 1; i < this.brafPool.length; i++) {
            this.brafPool[i].close();
        }
        
        // create temporary file
        File tmpFile = new File(this.filename + ".tmp");
	tmpFile.delete();
        RandomAccessFile tmpRAF = new BufferedRandomAccessFile(tmpFile, "rw");
        RandomAccessFile raf = this.brafPool[0]; raf.seek(0);

        // merge
        this.mergeNewEntries(buff, buff.length, raf, tmpRAF);

        // clean up
        raf.close();
        tmpRAF.close();
        String realName = this.getFPFilename();
        File currFile = new File(realName);
        currFile.delete();
        boolean status = tmpFile.renameTo(currFile);
        Assert.check(status, EC.SYSTEM_UNABLE_NOT_RENAME_FILE);

        // reopen a BufferedRAF for each thread
        for (int i = 0; i < this.braf.length; i++) {
            // Better way would be to provide method BRAF.open
            this.braf[i] = new BufferedRandomAccessFile(realName, "r");
        }
        for (int i = 0; i < this.brafPool.length; i++) {
            // Better way would be to provide method BRAF.open
            this.brafPool[i] = new BufferedRandomAccessFile(realName, "r");
        }
	this.poolIndex = 0;
    }

    private final void mergeNewEntries(long[] buff, int buffLen) throws IOException
    {
      // create temporary file
      File tmpFile = new File(this.filename + ".tmp");
      tmpFile.delete();
      RandomAccessFile tmpRAF = new BufferedRandomAccessFile(tmpFile, "rw");
      File currFile = new File(this.getFPFilename());
      RandomAccessFile currRAF = new BufferedRandomAccessFile(currFile, "r");

      // merge
      this.mergeNewEntries(buff, buffLen, currRAF, tmpRAF);

      // clean up
      currRAF.close();
      tmpRAF.close();
      currFile.delete();
      boolean status = tmpFile.renameTo(currFile);
      Assert.check(status, EC.SYSTEM_UNABLE_NOT_RENAME_FILE);
    }
  
    private int currIndex;
    private int counter;
    private final void writeFP(RandomAccessFile outRAF, long fp) throws IOException {
        outRAF.writeLong(fp);
        if (this.counter == 0) {
            this.index[this.currIndex++] = fp;
            this.counter = NumEntriesPerPage;
        }
        this.counter--;
    }
    
    
    private final void mergeNewEntries(long[] buff, int buffLen,
				       RandomAccessFile inRAF,
				       RandomAccessFile outRAF) throws IOException
    {
        // Precompute the maximum value of the new file
        long maxVal = buff[buffLen - 1];
        if (this.index != null) {
            maxVal = Math.max(maxVal, this.index[this.index.length - 1]);
        }

        int indexLen = (int)((this.fileCnt + buffLen - 1) / NumEntriesPerPage) + 2;
        this.index = new long[indexLen];
        this.index[indexLen - 1] = maxVal;
        this.currIndex = 0;
        this.counter = 0;

        // initialize positions in "buff" and "inRAF"
        int i = 0;
        long value = 0L; // initialize only to make compiler happy
        boolean eof = false;
        if (this.fileCnt > 0) {
            try {
                value = inRAF.readLong();
            } catch (EOFException e) 
            { 
                eof = true; 
            }
        } else {
            eof = true;
        }

        // merge while both lists still have elements remaining
        while (!eof && i < buffLen) 
        {
            if (value < buff[i]) 
            {
                this.writeFP(outRAF, value);
                try 
                {
                    value = inRAF.readLong();
                } catch (EOFException e) 
                { 
                    eof = true; 
                }
            } else 
            {
                Assert.check(value != buff[i], EC.TLC_FP_VALUE_ALREADY_ON_DISK, String.valueOf(value));
                this.writeFP(outRAF, buff[i++]);
            }
        }

        // write elements of remaining list
        if (eof) {
            while (i < buffLen) 
            {
                this.writeFP(outRAF, buff[i++]);
            }
        } else 
        {
            do 
            {
                this.writeFP(outRAF, value);
                try {
                    value = inRAF.readLong();
                } catch (EOFException e) { eof = true; }
            } while (!eof);
        }
        Assert.check(this.currIndex == indexLen - 1, EC.SYSTEM_INDEX_ERROR);

        // maintain object invariants
        this.fileCnt += buffLen;
    }
  
    public final void close() {
      for (int i = 0; i < this.braf.length; i++) {
	try {
	  this.braf[i].close();
	}
	catch (IOException e) { /*SKIP*/ }
      }
      for (int i = 0; i < this.brafPool.length; i++) {
	try {
	  this.brafPool[i].close();
	}
	catch (IOException e) { /*SKIP*/ }
      }
      this.poolIndex = 0;
    }

    public final void exit(boolean cleanup) throws IOException {
      if (cleanup) {
	// Delete the metadata directory:
	FileUtil.deleteDir(this.metadir, true);
      }
      String hostname = InetAddress.getLocalHost().getHostName();    
      MP.printMessage(EC.TLC_FP_COMPLETED, hostname);
      
      System.exit(0);    
    }

    public final double checkFPs() throws IOException {
      this.flushTable();    // No need for any lock here
      BufferedRandomAccessFile braf = new BufferedRandomAccessFile(this.getFPFilename(), "r");
      long fileLen = braf.length();
      long dis = Long.MAX_VALUE;
      if (fileLen > 0) {
	long x = braf.readLong();
	while (braf.getFilePointer() < fileLen) {
	  long y = braf.readLong();
	  long dis1 = y-x;
	  if (dis1 >= 0) {
	    dis = Math.min(dis, dis1);
	  }
	  x = y;
	}
      }
      braf.close();
      return (1.0/dis);
    }
    
    public final void beginChkpt(String fname) throws IOException {
      synchronized(this.rwLock) {
	this.flusherChosen = true;
	this.rwLock.BeginWrite();
	this.flushTable();
	FileUtil.copyFile(this.getFPFilename(), this.getChkptName(fname, "tmp"));
	this.rwLock.EndWrite();
	this.flusherChosen = false;
      }
    }

    public final void commitChkpt(String fname) throws IOException {
      File oldChkpt = new File(this.getChkptName(fname, "chkpt"));
      File newChkpt = new File(this.getChkptName(fname, "tmp"));
      if (!newChkpt.renameTo(oldChkpt)) {
	throw new IOException("DiskFPSet.commitChkpt: cannot delete " + oldChkpt);
      }
    }

    public final void recover(String fname) throws IOException {
        BufferedRandomAccessFile chkptRAF = 
            new BufferedRandomAccessFile(this.getChkptName(fname, "chkpt"), "r");
        BufferedRandomAccessFile currRAF = 
            new BufferedRandomAccessFile(this.getFPFilename(), "rw");

        this.fileCnt = chkptRAF.length() / LongSize;
        int indexLen = (int)((this.fileCnt - 1) / NumEntriesPerPage) + 2;
        this.index = new long[indexLen];
        this.currIndex = 0;
        this.counter = 0;

        long fp = 0L;
        try {
            while (true) {
                fp = chkptRAF.readLong();
                this.writeFP(currRAF, fp);
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
            this.braf[i] = new BufferedRandomAccessFile(this.getFPFilename(), "r");
        }
        for (int i = 0; i < this.brafPool.length; i++) {
            // Better way would be to provide method BRAF.open
   	    // close and reopen
	    this.brafPool[i].close();
            this.brafPool[i] = new BufferedRandomAccessFile(this.getFPFilename(), "r");
        }
	this.poolIndex = 0;
    }

    public final void beginChkpt() throws IOException { /*SKIP*/ }

    public final void commitChkpt() throws IOException { /*SKIP*/ }

    private long[] recoveryBuff = null;
    private int recoveryIdx = -1;
  
    public final void prepareRecovery() throws IOException {
      // First close all "this.braf" and "this.brafPool" objects on currName:
      for (int i = 0; i < this.braf.length; i++) {
	this.braf[i].close();
      }
      for (int i = 0; i < this.brafPool.length; i++) {
        this.brafPool[i].close();
      }

      recoveryBuff = new long[1<<21];
      recoveryIdx = 0;
    }

    public final void recoverFP(long fp) throws IOException
    {
      recoveryBuff[recoveryIdx++] = (fp & 0x7FFFFFFFFFFFFFFFL);
      if (recoveryIdx == recoveryBuff.length) {
	Sort.LongArray(recoveryBuff, recoveryIdx);
	this.mergeNewEntries(recoveryBuff, recoveryIdx);
	recoveryIdx = 0;
      }
    }
  
    public final void completeRecovery() throws IOException {
      Sort.LongArray(recoveryBuff, recoveryIdx);
      this.mergeNewEntries(recoveryBuff, recoveryIdx);
      recoveryBuff = null;
      recoveryIdx = -1;

      // Reopen a BufferedRAF for each thread
      for (int i = 0; i < this.braf.length; i++) {
	this.braf[i] = new BufferedRandomAccessFile(this.getFPFilename(), "r");
      }
      for (int i = 0; i < this.brafPool.length; i++) {
	this.brafPool[i] = new BufferedRandomAccessFile(this.getFPFilename(), "r");
      }
      this.poolIndex = 0;
    }
  
    public final void recover() throws IOException {
      this.prepareRecovery();
      
      long recoverPtr = TLCTrace.getRecoverPtr();
      BufferedRandomAccessFile braf = new BufferedRandomAccessFile(TLCTrace.getFilename(), "r");
      while (braf.getFilePointer() < recoverPtr) {
	braf.readLongNat();      /*drop*/
	long fp = braf.readLong();
	this.recoverFP(fp);
      }

      this.completeRecovery();
    }

    private String getChkptName(String fname, String name) 
    {
      return this.metadir + FileUtil.separator + fname + ".fp." + name;
    }

    private String getFPFilename() {
        return this.filename + ".fp";
    }

//  /**
//  * 
//  */
// private final void mergeBuff(long[] buff, int len, File fpFile)
// throws IOException {
//   File tmpFile = new File(this.filename + ".tmp");
//   tmpFile.delete();
//   BufferedRandomAccessFile fpRAF = new BufferedRandomAccessFile(fpFile, "rw");
//   BufferedRandomAccessFile tmpRAF = new BufferedRandomAccessFile(tmpFile, "rw");
//   int i = 0;
//   long value = 0L;
//   try {
//value = fpRAF.readLong();
//while (i < len) {
// if (value < buff[i]) {
//   tmpRAF.writeLong(value);
//   value = fpRAF.readLong();
// }
// else {
//   tmpRAF.writeLong(buff[i++]);
// }
//}
//   } catch (EOFException e) { /*SKIP*/ }
//
//   if (i < len) {
//for (int j = i; j < len; j++) {
// tmpRAF.writeLong(buff[j]);
//}
//   }
//   else {
//try {
// do {
//   tmpRAF.writeLong(value);
//   value = fpRAF.readLong();
// } while (true);
//} catch (EOFException e) { /*SKIP*/ }
//   }
//
//   fpRAF.close();
//   tmpRAF.close();
//   fpFile.delete();
//   tmpFile.renameTo(fpFile);
// }

}
