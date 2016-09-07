// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.EOFException;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.rmi.RemoteException;
import java.util.NoSuchElementException;
import java.util.concurrent.BrokenBarrierException;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.logging.Level;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.management.DiskFPSetMXWrapper;
import util.Assert;

/**
 * see OpenAddressing.tla
 */
@SuppressWarnings({ "serial" })
public final class OffHeapDiskFPSet extends NonCheckpointableDiskFPSet implements FPSetStatistic {
	
	private static final int PROBE_LIMIT = Integer.getInteger(OffHeapDiskFPSet.class.getName() + ".probeLimit", 128);
	static final long EMPTY = 0L;
	
	private final AtomicInteger reprobe;

	private final LongArray array;
	
	/**
	 * The indexer maps a fingerprint to a in-memory bucket and the associated lock
	 */
	private final Indexer indexer;

	private CyclicBarrier barrier;

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
		
		// This barrier gets run after one thread signals the need to suspend
		// put and contains operations to evict to secondary. Signaling is done
		// via the flusherChoosen AtomicBoolean. All threads (numThreads) will
		// then await on the barrier and the Runnable be executed when the
		// last of numThreads arrives.
		// Compared to an AtomicBoolean, the barrier operation use locks and
		// are thus comparably expensive.
		barrier = new CyclicBarrier(numThreads, new Runnable() {
			public void run() {
				// statistics
				growDiskMark++;
				final long timestamp = System.currentTimeMillis();
				final long insertions = tblCnt.longValue();
				final double lf = tblCnt.doubleValue() / (double) maxTblCnt;
				final int r = reprobe.intValue();

				// Atomically evict and reset flusherChosen to make sure no
				// thread re-read flusherChosen=true after an eviction and
				// wait again.
				try {
					flusher.flushTable(); // Evict()
				} catch (Exception notExpectedToHappen) {
					notExpectedToHappen.printStackTrace();
				} 

				long l = System.currentTimeMillis() - timestamp;
				flushTime += l;
				
				LOGGER.log(Level.FINE,
						"Flushed disk {0} {1}. time, in {2} sec after {3} insertions, load factor {4} and reprobe of {5}.",
						new Object[] { ((DiskFPSetMXWrapper) diskFPSetMXWrapper).getObjectName(), getGrowDiskMark(), l,
								insertions, lf, r });

				// Release exclusive access.
				flusherChosen.set(false);
			}
		});
	}

	private boolean checkEvictPending() {
		if (flusherChosen.get()) {
			try {
				barrier.await();
			} catch (InterruptedException notExpectedToHappen) {
				notExpectedToHappen.printStackTrace();
			} catch (BrokenBarrierException notExpectedToHappen) {
				notExpectedToHappen.printStackTrace();
			}
			return true;
		}
		return false;
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
	final boolean memLookup(final long fp0) {
		int r = reprobe.get() + 1;
		for (int i = 0; i < r; i++) {
			final long position = indexer.getIdx(fp0, i);
			final long l = array.get(position);
			if (fp0 == (l & FLUSHED_MASK)) {
				// zero the long msb (which is 1 if fp has been flushed to disk)
				return true;
			} else 	if (l == EMPTY) {
				return false;
			}
			r = reprobe.get() + 1;
		}

		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#memInsert(long)
	 */
	final boolean memInsert(final long fp0) throws IOException {
		// Try to insert into primary, Duplicate of memInsert
		for (int i = 0; i < PROBE_LIMIT; i++) {
			final long position = indexer.getIdx(fp0, i);
			final long expected = array.get(position);
			if (expected == EMPTY || (expected < 0 && fp0 != (expected & FLUSHED_MASK))) {
				// Increment reprobe if needed. Other threads might have
				// increased concurrently. Since reprobe is strictly
				// monotonic increasing, we need no retry when r larger.
				int r = reprobe.get();
				while (i > r && !reprobe.compareAndSet(r, i)) {
					r = reprobe.get();
				}
				
				// Try to CAS the new fingerprint. In case of failure, reprobe
				// is too large which we ignore.
				if (array.trySet(position, expected, fp0)) {
					this.tblCnt.getAndIncrement();
					return false;
				}
				// Cannot reduce reprobe to its value before we increased it.
				// Another thread could have caused an increase to i too which
				// would be lost.
			}
			
			// Expected is the fingerprint to be inserted.
			if ((expected & FLUSHED_MASK) == fp0) {
				return true;
			}
		}

		
		// We failed to insert into primary. Consequently, lets try and make
		// some room by signaling all threads to wait for eviction.
		forceFlush();
		// We've signaled for eviction to start or failed because some other
		// thread beat us to it. Actual eviction and setting flusherChosen back
		// to false is done by the Barrier's Runnable. We cannot set
		// flusherChosen back to false after barrier.awaits returns because it
		// leaves a window during which other threads read the old true value of
		// flusherChosen a second time and immediately wait again.
		
		return put(fp0);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#put(long)
	 */
	public final boolean put(final long fp) throws IOException {
		if (checkEvictPending()) { return put(fp); }

		// zeros the msb
		final long fp0 = fp & FLUSHED_MASK;

		// Only check primary and disk iff there exists a disk file. index is
		// created when we wait and thus cannot race.
		if (index != null) {
			// Lookup primary memory
			if (memLookup(fp0)) {
				this.memHitCnt.getAndIncrement();
				return true;
			}
			
			// Lookup on disk
			if (this.diskLookup(fp0)) {
				this.diskHitCnt.getAndIncrement();
				return true;
			}
		}
		
		// Lastly, try to insert into memory.
		return memInsert(fp0);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#contains(long)
	 */
	public final boolean contains(final long fp) throws IOException {
		// maintains happen-before with regards to successful put
		
		if (checkEvictPending()) { return contains(fp);	}

		// zeros the msb
		final long fp0 = fp & FLUSHED_MASK;
		
		// Lookup in primary
		if (memLookup(fp0)) {
			return true;
		}
		
		// Lookup on secondary/disk
		if(this.diskLookup(fp0)) {
			diskHitCnt.getAndIncrement();
			return true;
		}
		
		return false;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#forceFlush()
	 */
	public void forceFlush() {
		flusherChosen.compareAndSet(false, true);
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
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#getOverallCapacity()
	 */
	public long getOverallCapacity() {
		return array.size();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#getBucketCapacity()
	 */
	public long getBucketCapacity() {
		// A misnomer, but bucketCapacity is obviously not applicable with open
		// addressing.
		return reprobe.longValue();
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
			final SortingIterator itr = new SortingIterator(array, buffLen, reprobe.get(), indexer);

			// Precompute the maximum value of the new file. DiskFPSet#writeFP
			// updates the index on the fly.
			final int indexLen = calculateIndexLen(buffLen);
			index = new long[indexLen];
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

			// After flush, we might be able to reduce reprobe. It is possible
			// to even set it to zero and make all lookups go to secondary.
			reprobe.set(itr.getReprobe());
			
			// Update the last element in index with the large one of the
			// current largest element of itr and the previous largest element.
			index[indexLen - 1] = Math.max(fp, index[index.length - 1]);

			// both sets used up completely
			Assert.check(eof && eol, EC.GENERAL);

			// currIndex is amount of disk writes
			Assert.check(currIndex == indexLen - 1, EC.SYSTEM_INDEX_ERROR);

			// maintain object invariants
			fileCnt += buffLen;
		}
	}
	
	/**
	 * A non-thread safe Iterator whose next method returns the next largest
	 * element.
	 */
	public static class SortingIterator {
		private final long elements;
		private final LongArray array;
		private final Indexer indexer;
		private final int reprobe;

		private int newReprobe;
		private long idx = 0;
		private long elementsRead = 0L;
		
		public SortingIterator(final LongArray array, final long elements, final int reprobe, final Indexer indexer) {
			this.array = array;
			this.elements = elements;
			this.reprobe = reprobe;
			this.newReprobe = reprobe;
			this.indexer = indexer;
		}

		/**
		 * Returns the next element in the iteration that is not EMPTY nor
		 * marked evicted.
		 * <p>
		 * THIS IS NOT SIDEEFFECT FREE. AFTERWARDS, THE ELEMENT WILL BE MARKED
		 * EVICTED.
		 *
		 * @return the next element in the iteration that is not EMPTY nor
		 *         marked evicted.
		 * @exception NoSuchElementException
		 *                iteration has no more elements.
		 */
		public long next() {
			if (elementsRead >= elements) {
				throw new NoSuchElementException();
			}
			
			long elem = EMPTY;
			do {
				sortLookahead();
				
				long position = idx % array.size();
				elem = array.get(position);
				
				final long baseIdx = indexer.getIdx(elem);
				if (elem > EMPTY && isSorted(baseIdx, elem, idx, reprobe, array.size())) {
					// mark elem in array as being evicted.
					array.set(position, elem | MARK_FLUSHED);

					newReprobe = (int) Math.min(newReprobe, idx - baseIdx);
					
					idx = idx + 1L;
					elementsRead = elementsRead + 1L;
					return elem;
				}
				
				idx = idx + 1L;
			} while (hasNext());
			
			// make compiler happy
			throw new NoSuchElementException();
		}

		// This is a variant of selection sort O(n^2) which skips negative and
		// empty positions.
		private void sortLookahead() {
			final long lo = array.get(idx % array.size());
			int r = 1;
			while (r <= reprobe) {
				final long hi = array.get((idx + r) % array.size());
				final long idxLo = indexer.getIdx(lo);
				final long idxHi = indexer.getIdx(hi);
				if (compare(idxLo, lo, idx, idxHi, hi, r, reprobe, array.size())) {
					array.swap(idx % array.size(), (idx + r) % array.size());
				}
				r = r + 1;
			}
		}
		
	    /**
	     * Returns <tt>true</tt> if the iteration has more elements. (In other
	     * words, returns <tt>true</tt> if <tt>next</tt> would return an element
	     * rather than throwing an exception.)
	     *
	     * @return <tt>true</tt> if the iterator has more elements.
	     */
		public boolean hasNext() {
			return elementsRead < elements;
		}
		
		public int getReprobe() {
			// returns the maximum displacement of fingerprints.
			return newReprobe;
		}
		
		//******** static helpers ********//
		
		/**
	     * A fp wrapped around if its alternate indices are beyond
	     * K and its actual index is lower than its primary idx.	 
	     */
		private static boolean wrapped(final long idx, final long fp, final long pos, final int p, final long k) {
			// /\ idx(fp,0) + P > K
			// /\ idx(fp,0) > mod(pos, K)
			return idx + p > k && idx > (pos % k);
		}

		/**
		 * TRUE iff the given two fingerprints have to be swapped to satisfy the
		 * expected order.
		 */
		private static boolean compare(final long idxLo, final long fpLo, final long outer, final long idxHi, final long fpHi,
				final long inner, final int p, final long k) {
			if (fpLo <= EMPTY || fpHi <= EMPTY) {
				return false;
			}
			final long posLo = outer % k;
			final long posHi = (outer + inner) % k;
			final boolean wrappedLo = wrapped(idxLo, fpLo, outer, p, k);
			final boolean wrappedHi = wrapped(idxHi, fpHi, outer + inner, p, k);
			if (fpLo < fpHi && posLo > posHi && !(wrappedLo ^ wrappedHi)) {
				// /\ fp1 < fp2
				// /\ mod(i1, K) > mod(i1+i2, K)
				// /\ wrapped(fp1,i1, P) <=> wrapped(fp2,i1+i2, P)
				return true;
			} else if (fpLo > fpHi && posLo > posHi && idxLo == idxHi) {
				// /\ fp1 > fp2
				// /\ mod(i1, K) > mod(i1+i2, K)
				// /\ idx(fp1,0) = idx(fp2, 0)
				return true;
			} else if (fpLo > fpHi && posLo < posHi && idxLo >= idxHi && !(wrappedLo ^ wrappedHi)) {
				// /\ fp1 > fp2
				// /\ mod(i1, K) < mod(i1+i2, K)
				// /\ idx(fp1,0) >= idx(fp2, 0)
				// /\ wrapped(fp1,i1, P) <=> wrapped(fp2,i1+i2, P)
				return true;
			} else if (fpLo > fpHi && posLo > posHi && idxLo > idxHi && (wrappedLo ^ wrappedHi)) {
				// /\ fp1 > fp2
				// /\ mod(i1, K) > mod(i1+i2, K)
				// /\ idx(fp1,0) > idx(fp2, 0)
				// /\ ~(wrapped(fp1,i1, P) <=> wrapped(fp2,i1+i2, P))
				return true;
			}
			return false;
		}

		private static boolean isSorted(final long idx, final long elem, final long outer, final int p, final long k) {
			final boolean wrapped = wrapped(idx, elem, outer, p, k);
			return ((outer < k && !wrapped) || (outer >= k && wrapped));
		}
	}
}
