// Copyright (c) 2012 Microsoft Corporation. All rights reserved.
package tlc2.tool.fp;

import java.io.IOException;
import java.rmi.RemoteException;
import java.util.concurrent.locks.Lock;
import java.util.logging.Level;

import tlc2.TLCGlobals;
import tlc2.tool.fp.management.DiskFPSetMXWrapper;
import tlc2.util.Striped;
import util.Assert;

@SuppressWarnings("serial")
public abstract class HeapBasedDiskFPSet extends DiskFPSet {

	/**
	 * Number of locks in the striped lock (#StripeLocks = 2^LogLockCnt).<br>
	 * Theoretically best performance should be seen with on lock per bucket in
	 * the primary hash table. An some point though (not yet measured), this
	 * performance benefit is probably eaten up by the memory consumption of the
	 * striped lock {@link DiskFPSet#rwLock} itself, which reduces the memory
	 * available to the hash set.
	 */
	protected static final int LogLockCnt = Integer.getInteger(DiskFPSet.class.getName() + ".logLockCnt", (31 - Integer.numberOfLeadingZeros(TLCGlobals.getNumWorkers()) + 8));
	/**
	 * protects n memory buckets
	 */
	protected final Striped rwLock;
	/**
	 * Is (1 << LogLockCnt) and exposed here for subclasses
	 */
	protected final int lockCnt;
	
	protected final int lockMask;
	/**
	 * in-memory buffer of new entries
	 */
	protected long[][] tbl;
	
	/**
	 * mask for computing hash function
	 */
	protected long mask;
	
	/**
	 * The calculated capacity of tbl. Will always be a power of two.
	 */
	protected final int capacity;
	
	/**
	 * 
	 */
	protected int logMaxMemCnt;

	protected static final int BucketSizeIncrement = 4;
	/**
	 * Log (base 2) of default number of new entries allowed to accumulate in
	 * memory before those entries are flushed to disk.
	 */
	protected static final int LogDefaultMaxTblCnt = 19;
	static final int DefaultMaxTblCnt = (1 << LogDefaultMaxTblCnt);

	protected HeapBasedDiskFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
		super(fpSetConfig);

		// Ideally we use one lock per bucket because even with relatively high
		// lock counts, we fall victim to the birthday paradox. However, locks
		// ain't cheap, which is why we have to find the sweet spot. We
		// determined the constant 8 empirically on Intel Xeon CPU E5-2670 v2 @
		// 2.50GHz. This is based on the number of cores only. We ignore their
		// speed. MultiThreadedMSBDiskFPSet is the most suitable performance
		// test available for the job. It just inserts long values into the
		// set. int is obviously going to be too small once 2^23 cores become
		// commonplace.
		this.lockCnt = 1 << LogLockCnt;
		this.rwLock = Striped.readWriteLock(lockCnt);

		// Reserve a portion of the memory for the auxiliary storage
		long maxMemCnt = (long) (fpSetConfig.getMemoryInFingerprintCnt() / getAuxiliaryStorageRequirement());

		// default if not specific value given
		if ((maxMemCnt - LogMaxLoad) <= 0) {
			maxMemCnt = DefaultMaxTblCnt;
		}
		
		// approximate next lower 2^n ~= maxMemCnt
		logMaxMemCnt = (Long.SIZE - 1) - Long.numberOfLeadingZeros(maxMemCnt);
		
		// guard against underflow
		// LL modified error message on 7 April 2012
		Assert.check(logMaxMemCnt - LogMaxLoad >= 0, "Underflow when computing HeapBasedDiskFPSet");
		
		// Guard against a capacity overflow with large amounts (e.g. ~1TB) of
		// dedicated memory. If cap overflows, the VMs maximum allowed array
		// size is used.
		final int cap = 1 << (logMaxMemCnt - LogMaxLoad);
		if (cap < 0) {
			// You wonder why 8 and not 42? Ask the VM gods!
			this.capacity = Integer.MAX_VALUE - 8;
		} else {
			this.capacity = cap;
		}
		
		// maxTblCnt mathematically has to be an upper limit for the in-memory storage 
		// so that a disk flush occurs before an _evenly_ distributed fp distribution fills up 
		// the collision buckets to a size that exceeds the VM limit (unevenly distributed 
		// fp distributions can still cause a OutOfMemoryError which this guard).
		this.maxTblCnt = (1L << logMaxMemCnt); // maxTblCnt := 2^logMaxMemCnt

		Assert.check(maxTblCnt <= fpSetConfig.getMemoryInFingerprintCnt(), "Exceeded upper memory storage limit");

		// guard against negative maxTblCnt
		// LL modified error message on 7 April 2012
		Assert.check(maxTblCnt > capacity && capacity > getTblCnt(),
				"negative maxTblCnt");

		this.mask = capacity - 1;
		
		this.lockMask = lockCnt - 1;

		this.tbl = new long[capacity][];
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#sizeof()
	 */
	public long sizeof() {
		long size = 44; // approx size of this DiskFPSet object
		rwLock.acquireAllLocks();
		size += 16 + (this.tbl.length * 4); // for this.tbl
		for (int i = 0; i < this.tbl.length; i++) {
			if (this.tbl[i] != null) {
				// 16 bytes overhead for each row in tbl!
				size += 16 + (this.tbl[i].length * (long) LongSize);
			}
		}
		// size of index array if non-null
		size += getIndexCapacity() * 4;
		rwLock.releaseAllLocks();
		return size;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#getLockCnt()
	 */
	public int getLockCnt() {
		return this.rwLock.size();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#getTblCapacity()
	 */
	public long getTblCapacity() {
		return tbl.length;
	}

	/**
	 * calculate hash value (just n least significat bits of fp) which is used as an index address
	 * @param fp
	 * @return
	 */
	protected int getIndex(long fp) {
		return (int) index(fp, this.mask);
		
	}	
	
	protected int getLockIndex(long fp) {
		// In case of overflow, a NegativeArrayOffset will be thrown
		// subsequently.
		return (int) index(fp, this.lockMask);
	}
	
	protected long index(long fp, long aMask) {
		return fp & aMask;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#contains(long)
	 * 
     * 0 and {@link Long#MIN_VALUE} always return false
	 */
	public final boolean contains(long fp) throws IOException {
		fp = checkValid(fp);
		// zeros the msb
		long fp0 = fp & 0x7FFFFFFFFFFFFFFFL;
		final Lock readLock = this.rwLock.getAt(getLockIndex(fp0)).readLock();
		readLock.lock();
		// First, look in in-memory buffer
		if (this.memLookup(fp0)) {
			readLock.unlock();
			this.memHitCnt.increment();
			return true;
		}

		// block if disk is being re-written
		// next, look on disk
		boolean diskHit = this.diskLookup(fp0);
		// increment while still locked
		if(diskHit) {
			diskHitCnt.increment();
		}

		// end read; add to memory buffer if necessary
		readLock.unlock();
		return diskHit;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#memLookup(long)
	 */
	boolean memLookup(long fp) {
		long[] bucket = this.tbl[getIndex(fp)];
		if (bucket == null)
			return false;

		int bucketLen = bucket.length;
		// Linearly search the bucket; 0L is an invalid fp and marks the end of
		// the allocated bucket
		for (int i = 0; i < bucketLen && bucket[i] != 0L; i++) {
			// zero the long msb (which is 1 if fp has been flushed to disk)
			if (fp == (bucket[i] & 0x7FFFFFFFFFFFFFFFL))
				return true;
		}
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#put(long)
	 * 
     * 0 and {@link Long#MIN_VALUE} always return false
     * 
     * Locking is as follows:
     * 
     * Acquire mem read lock
     * Acquire disk read lock
     * Release mem read lock
     * 
     * Acquire mem read/write lock
     * Release disk read lock // interleaved 
     *  insert into mem
     * Acquire disk write lock (might cause potential writer to wait() which releases mem read lock (monitor))
     * 	flushToDisk
     * Release disk write lock
     * Release mem read lock
     * 
     * asserts:
     * - Exclusive access to disk and memory for a writer
     * 
	 */
	public final boolean put(long fp) throws IOException {
		fp = checkValid(fp);
		// zeros the msb
		long fp0 = fp & 0x7FFFFFFFFFFFFFFFL;
		
		final Lock readLock = rwLock.getAt(getLockIndex(fp0)).readLock();
		readLock.lock();
		// First, look in in-memory buffer
		if (this.memLookup(fp0)) {
			readLock.unlock();
			this.memHitCnt.increment();
			return true;
		}
		
		// blocks => wait() if disk is being re-written 
		// (means the current thread returns rwLock monitor)
		// Why not return monitor first and then acquire read lock?
		// => prevent deadlock by acquiring threads in same order? 
		
		// next, look on disk
		boolean diskHit = this.diskLookup(fp0);
		
		// In event of disk hit, return
		if (diskHit) {
			readLock.unlock();
			this.diskHitCnt.increment();
			return true;
		}
		
		readLock.unlock();
		
		// Another writer could write the same fingerprint here if it gets
		// interleaved. This is no problem though, because memInsert again
		// checks existence for fp to be inserted
		
		final Lock w = rwLock.getAt(getLockIndex(fp0)).writeLock();
		w.lock();
		
		// if disk lookup failed, add to memory buffer
		if (this.memInsert(fp0)) {
			w.unlock();
			this.memHitCnt.increment();
			return true;
		}
		
		// test if buffer is full && block until there are no more readers 
		if (needsDiskFlush() && this.flusherChosen.compareAndSet(false, true)) {
			
			// statistics
			growDiskMark++;
			final long timestamp = System.currentTimeMillis();
			final long insertions = getTblCnt();
			
			// acquire _all_ write locks
			rwLock.acquireAllLocks();
			
			// flush memory entries to disk
			flusher.flushTable();
			
			// release _all_ write locks
			rwLock.releaseAllLocks();
			
			// reset forceFlush to false
			forceFlush = false;
			
			// finish writing
			this.flusherChosen.set(false);

			long l = System.currentTimeMillis() - timestamp;
			flushTime += l;
			
			LOGGER.log(Level.FINE, "Flushed disk {0} {1}. time, in {2} sec after {3} insertions.", new Object[] {
					((DiskFPSetMXWrapper) diskFPSetMXWrapper).getObjectName(), getGrowDiskMark(), l, insertions});
		}
		w.unlock();
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#memInsert(long)
	 */
	boolean memInsert(long fp) {
		int index = getIndex(fp);
		
		// try finding an existing bucket 
		long[] bucket = this.tbl[index];
		
		// no existing bucket found, create new one
		if (bucket == null) {
			bucket = new long[InitialBucketCapacity];
			bucket[0] = fp;
			this.tbl[index] = bucket;
			this.bucketsCapacity += InitialBucketCapacity; 
			this.tblLoad.increment();
		} else {
			// search for entry in existing bucket
			int bucketLen = bucket.length;
			int i = -1;
			int j = 0;
			for (; j < bucketLen && bucket[j] != 0L; j++) {
				long fp1 = bucket[j];
				// zero the long msb
				long l = fp1 & 0x7FFFFFFFFFFFFFFFL;
				if (fp == l) {
					// found in existing bucket
					return true;
				}
				// fp1 < 0 iff fp1 is on disk;
				// In this case, keep fp1 idx for new fingerprint fp
				if (i == -1 && fp1 < 0) {
					i = j;
				}
			}
			if (i == -1) {
				if (j == bucketLen) {
					// bucket is full; grow the bucket by BucketSizeIncrement
					long[] oldBucket = bucket;
					bucket = new long[bucketLen + BucketSizeIncrement];
					System.arraycopy(oldBucket, 0, bucket, 0, bucketLen);
					this.tbl[index] = bucket;
					this.bucketsCapacity += BucketSizeIncrement;
				}
				// add to end of bucket
				bucket[j] = fp;
			} else {
				if (j != bucketLen) {
					bucket[j] = bucket[i];
				}
				bucket[i] = fp;
			}
		}
		this.tblCnt.increment();
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#acquireTblWriteLock()
	 */
	void acquireTblWriteLock() {
		rwLock.acquireAllLocks();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#releaseTblWriteLock()
	 */
	void releaseTblWriteLock() {
		rwLock.releaseAllLocks();
	}
}
