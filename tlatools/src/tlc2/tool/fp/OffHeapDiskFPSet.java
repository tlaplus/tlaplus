// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.EOFException;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.rmi.RemoteException;
import java.util.NoSuchElementException;
import java.util.concurrent.atomic.AtomicInteger;

import tlc2.output.EC;
import tlc2.output.MP;
import util.Assert;

@SuppressWarnings({ "serial" })
public final class OffHeapDiskFPSet extends NonCheckpointableDiskFPSet implements FPSetStatistic {
	
	private final AtomicInteger reprobe;

	private final LongArray array;
	
	/**
	 * The indexer maps a fingerprint to a in-memory bucket and the associated lock
	 */
	private final Indexer indexer;

	protected OffHeapDiskFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
		super(fpSetConfig);
		
		final long positions = fpSetConfig.getMemoryInFingerprintCnt();
		
		// Determine base address which varies depending on machine architecture.
		this.array = new LongArray(positions);
		this.reprobe = new AtomicInteger(0);
		
		this.flusher = new OffHeapMSBFlusher();
		
		// If Hamming weight is 1, the logical index address can be calculated
		// significantly faster by bit-shifting. However, with large memory
		// sizes, only supporting increments of 2^n sizes would waste memory
		// (e.g. either 32GiB or 64Gib). Hence, we check if the bitCount allows
		// us to use bit-shifting. If not, we fall back to less efficient
		// calculations.
		if (Long.bitCount(positions) == 1) {
			this.indexer = new BitshiftingIndexer(positions, fpSetConfig.getFpBits());
		} else {
			// non 2^n buckets cannot use a bit shifting indexer
			this.indexer = new Indexer(positions, fpSetConfig.getFpBits());
		}
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#init(int, java.lang.String, java.lang.String)
	 */
	public void init(int numThreads, String aMetadir, String filename)
			throws IOException {
		super.init(numThreads, aMetadir, filename);
		
		array.zeroMemory(numThreads);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#sizeof()
	 */
	public long sizeof() {
		long size = 44; // approx size of this DiskFPSet object
		size += maxTblCnt * (long) LongSize;
		size += getIndexCapacity() * 4;
		return size;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#needsDiskFlush()
	 */
	protected final boolean needsDiskFlush() {
		return loadFactorExceeds(1d) || forceFlush;
	}
	
	/**
	 * This limits the (primary) in-memory hash table to grow beyond the given
	 * limit.
	 * 
	 * @param limit
	 *            A limit in the domain [0, 1] which restricts the hash table
	 *            from growing past it.
	 * @return true iff the current hash table load exceeds the given limit
	 */
	private final boolean loadFactorExceeds(final double limit) {
		final double d = (this.tblCnt.doubleValue()) / (double) this.maxTblCnt;
		return d >= limit;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#memLookup(long)
	 */
	final boolean memLookup(long fp) {		
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#memInsert(long)
	 */
	final boolean memInsert(long fp) {
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#put(long)
	 */
	public final boolean put(final long fp) throws IOException {
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#contains(long)
	 */
	public final boolean contains(final long fp) throws IOException {
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#acquireTblWriteLock()
	 */
	void acquireTblWriteLock() {
		// no-op for now
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#releaseTblWriteLock()
	 */
	void releaseTblWriteLock() {
		// no-op for now
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#getTblCapacity()
	 */
	public long getTblCapacity() {
		return maxTblCnt;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#getTblLoad()
	 */
	public long getTblLoad() {
		return getTblCnt();
	}

	//**************************** Indexer ****************************//
	
	public static class Indexer {

		private static final long minFingerprint = 1L; //Minimum possible fingerprint (0L marks an empty position)

		private final float tblScalingFactor;
		private final long maxFingerprint;
		protected final long positions;
		
		public Indexer(final long positions, final int fpBits) {
			this(positions, fpBits, 0xFFFFFFFFFFFFFFFFL >>> fpBits);
		}

		public Indexer(final long positions, final int fpBits, final long maxValue) {
			this.positions = positions;
			this.maxFingerprint = maxValue;
			// (position-1L) because array is zero indexed.
			this.tblScalingFactor = (positions - 1L) / ((maxFingerprint - minFingerprint) * 1f);
		}
		
		protected long getIdx(final long fp) {
			return getIdx(fp, 0);
		}
		
		protected long getIdx(final long fp, final int probe) {
			long idx = Math.round(tblScalingFactor * (fp - minFingerprint)) + probe;
			return idx % positions;
		}
	}
	
	public static class BitshiftingIndexer extends Indexer {
		private final long prefixMask;
		private final int rShift;

		public BitshiftingIndexer(final long positions, final int fpBits) throws RemoteException {
			super(positions, fpBits);
			
			this.prefixMask = 0xFFFFFFFFFFFFFFFFL >>> fpBits;
			
			long n = (0xFFFFFFFFFFFFFFFFL >>> fpBits) - (positions - 1);
			int moveBy = 0;
			while (n >= positions) {
				moveBy++;
				n = n >>> 1; // == (n/2)
			}
			this.rShift = moveBy;
		}
		
		@Override
		protected long getIdx(final long fp) {
			return ((fp & prefixMask) >>> rShift);
		}
		
		@Override
		protected long getIdx(final long fp, int probe) {
			// Have to mod positions because probe might cause us to overshoot.
			return (((fp & prefixMask) >>> rShift) + probe) % positions; 
		}
	}

	//**************************** Flusher ****************************//
	
	public class OffHeapMSBFlusher extends Flusher {
		
		/* (non-Javadoc)
		 * @see tlc2.tool.fp.MSBDiskFPSet#mergeNewEntries(java.io.RandomAccessFile, java.io.RandomAccessFile)
		 */
		@Override
		protected void mergeNewEntries(RandomAccessFile[] inRAFs, RandomAccessFile outRAF) throws IOException {
			final long buffLen = tblCnt.get();
			ByteBufferIterator itr = new ByteBufferIterator(array, buffLen);

			// Precompute the maximum value of the new file
			long maxVal = itr.getLast();
			if (index != null) {
				maxVal = Math.max(maxVal, index[index.length - 1]);
			}

			int indexLen = calculateIndexLen(buffLen);
			index = new long[indexLen];
			index[indexLen - 1] = maxVal;
			currIndex = 0;
			counter = 0;

			// initialize positions in "buff" and "inRAF"
			long value = 0L; // initialize only to make compiler happy
			boolean eof = false;
			if (fileCnt > 0) {
				try {
					value = inRAFs[0].readLong();
				} catch (EOFException e) {
					eof = true;
				}
			} else {
				eof = true;
			}

			// merge while both lists still have elements remaining
			boolean eol = false;
			long fp = itr.next();
			while (!eof || !eol) {
				if ((value < fp || eol) && !eof) {
					writeFP(outRAF, value);
					try {
						value = inRAFs[0].readLong();
					} catch (EOFException e) {
						eof = true;
					}
				} else {
					// prevent converting every long to String when assertion holds (this is expensive)
					if (value == fp) {
						//MAK: Commented cause a duplicate does not pose a risk for correctness.
						// It merely indicates a bug somewhere.
						//Assert.check(false, EC.TLC_FP_VALUE_ALREADY_ON_DISK,
						//		String.valueOf(value));
						MP.printWarning(EC.TLC_FP_VALUE_ALREADY_ON_DISK, String.valueOf(value));
					}
					writeFP(outRAF, fp);
					// we used one fp up, thus move to next one
					try {
						fp = itr.next();
					} catch (NoSuchElementException e) {
						// has read all elements?
						Assert.check(!itr.hasNext(), EC.GENERAL);
						eol = true;
					}
				}
			}
			
			// both sets used up completely
			Assert.check(eof && eol, EC.GENERAL);

			// currIndex is amount of disk writes
			Assert.check(currIndex == indexLen - 1, EC.SYSTEM_INDEX_ERROR);

			// maintain object invariants
			fileCnt += buffLen;
		}
	}
	
	/**
	 * A non-thread safe Iterator 
	 */
	public class ByteBufferIterator {
		private final LongArray array;

		public ByteBufferIterator(LongArray helper, long expectedElements) {
			this.array = helper;
		}

	    /**
	     * Returns the next element in the iteration.
	     *
	     * @return the next element in the iteration.
	     * @exception NoSuchElementException iteration has no more elements.
	     */
		public long next() {
			throw new NoSuchElementException();
		}

	    /**
	     * Returns <tt>true</tt> if the iteration has more elements. (In other
	     * words, returns <tt>true</tt> if <tt>next</tt> would return an element
	     * rather than throwing an exception.)
	     *
	     * @return <tt>true</tt> if the iterator has more elements.
	     */
		public boolean hasNext() {
			return false;
		}
		
		/**
		 * @return The last element in the iteration.
	     * @exception NoSuchElementException if iteration is empty.
		 */
		public long getLast() {
			throw new NoSuchElementException();
		}
	}
}
