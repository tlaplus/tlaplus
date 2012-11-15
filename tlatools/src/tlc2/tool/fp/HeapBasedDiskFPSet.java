// Copyright (c) 2012 Microsoft Corporation. All rights reserved.
package tlc2.tool.fp;

import java.rmi.RemoteException;

import util.Assert;

@SuppressWarnings("serial")
public abstract class HeapBasedDiskFPSet extends DiskFPSet {
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
	 * The calculated capacity of tbl
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
		this.capacity = 1 << (logMaxMemCnt - LogMaxLoad);
		
		// instead of changing maxTblCnd to long and pay an extra price when 
		// comparing int and long every time put(long) is called, we set it to 
		// Integer.MAX_VALUE instead. capacity can never grow bigger 
		// (unless java starts supporting 64bit array sizes)
		//
		// maxTblCnt mathematically has to be an upper limit for the in-memory storage 
		// so that a disk flush occurs before an _evenly_ distributed fp distribution fills up 
		// the collision buckets to a size that exceeds the VM limit (unevenly distributed 
		// fp distributions can still cause a OutOfMemoryError which this guard).
		this.maxTblCnt = (logMaxMemCnt >= 31) ? Integer.MAX_VALUE : (1 << logMaxMemCnt); // maxTblCnt := 2^logMaxMemCnt

		Assert.check(maxTblCnt <= fpSetConfig.getMemoryInFingerprintCnt(), "Exceeded upper memory storage limit");

		// guard against negative maxTblCnt
		// LL modified error message on 7 April 2012
		Assert.check(maxTblCnt > capacity && capacity > tblCnt.get(),
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
			this.tblLoad++;
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
		this.tblCnt.getAndIncrement();
		return false;
	}
}
