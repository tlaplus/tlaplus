// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.EOFException;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.NoSuchElementException;
import java.util.concurrent.BrokenBarrierException;
import java.util.concurrent.Callable;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.atomic.LongAccumulator;
import java.util.function.LongBinaryOperator;
import java.util.logging.Level;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.LongArrays.LongComparator;
import tlc2.tool.fp.management.DiskFPSetMXWrapper;
import tlc2.util.Striped;
import util.Assert;

/**
 * see OpenAddressing.tla
 */
@SuppressWarnings({ "serial" })
public final class OffHeapDiskFPSet extends NonCheckpointableDiskFPSet implements FPSetStatistic {
	
	private static final int PROBE_LIMIT = Integer.getInteger(OffHeapDiskFPSet.class.getName() + ".probeLimit", 128);
	static final long EMPTY = 0L;
	
	private final LongAccumulator reprobe;

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
		this.reprobe = new LongAccumulator(new LongBinaryOperator() {
			public long applyAsLong(long left, long right) {
				return Math.max(left, right);
			}
		}, 0);
		
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
	public void init(final int numThreads, String aMetadir, String filename)
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
			// Atomically evict and reset flusherChosen to make sure no
			// thread re-read flusherChosen=true after an eviction and
			// waits again.
			public void run() {
				// statistics
				growDiskMark++;
				final long timestamp = System.currentTimeMillis();
				final long insertions = tblCnt.longValue();
				final double lf = tblCnt.doubleValue() / (double) maxTblCnt;
				final int r = reprobe.intValue();
				final long size = array.size();
				
				// Only pay the price of creating threads when array is sufficiently large.
				if (size > 8192) {
					final long length = (long) Math.floor(size / numThreads);
					final Striped striped = Striped.readWriteLock(numThreads);
					
					final Collection<Callable<Void>> tasks = new ArrayList<Callable<Void>>(numThreads);
					for (int i = 0; i < numThreads; i++) {
						final int offset = i;
						tasks.add(new Callable<Void>() {
							@Override
							public Void call() throws Exception {
								final long start = offset * length;
								final long end = offset == numThreads - 1 ? size - 1L : start + length - 1L;
								
								striped.getAt(offset).writeLock().lock();
								LongArrays.sort(array, start, end, getLongComparator());
								striped.getAt(offset).writeLock().unlock();
								
								striped.getAt(offset + 1 % numThreads).writeLock().lock();
								LongArrays.sort(array, end - r, end + r, getLongComparator());
								striped.getAt(offset + 1 % numThreads).writeLock().unlock();
								
								return null;
							}
						});
					}
					final ExecutorService executorService = Executors.newFixedThreadPool(numThreads);
					try {
						executorService.invokeAll(tasks);
					} catch (InterruptedException notExpectedToHappen) {
						notExpectedToHappen.printStackTrace();
					} finally {
						executorService.shutdown();
					}
				} else {
					// Sort with a single thread.
					LongArrays.sort(array, 0, size - 1L + r, getLongComparator());
				}
				
				// Write sorted table to disk in a single thread.
				try {
					flusher.flushTable(); // Evict()
				} catch (Exception notExpectedToHappen) {
					notExpectedToHappen.printStackTrace();
				} 

				// statistics and logging again.
				long l = System.currentTimeMillis() - timestamp;
				flushTime += l;
				LOGGER.log(Level.FINE,
						"Flushed disk {0} {1}. time, in {2} sec after {3} insertions, load factor {4} and reprobe of {5}.",
						new Object[] { ((DiskFPSetMXWrapper) diskFPSetMXWrapper).getObjectName(), getGrowDiskMark(), l,
								insertions, lf, r });

				// Release exclusive access. It has to be done by the runnable
				// before workers waiting on the barrier wake up again.
				flusherChosen.set(false);
			}

			private LongComparator getLongComparator() {
				return new LongComparator() {
					public int compare(long fpA, long posA, long fpB, long posB) {
						
						// Elements not in Nat \ {0} remain at their current
						// position.
						if (fpA <= EMPTY || fpB <= EMPTY) {
							return 0;
						}
						
						final boolean wrappedA = indexer.getIdx(fpA) > posA;
						final boolean wrappedB = indexer.getIdx(fpB) > posB;
						
						if (wrappedA == wrappedB && posA > posB) {
							return fpA < fpB ? -1 : 1;
						} else if ((wrappedA ^ wrappedB)) {
							if (posA < posB && fpA < fpB) {
								return -1;
							}
							if (posA > posB && fpA > fpB) {
								return -1;
							}
						}
						return 0;
					}
				};
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
		int r = reprobe.intValue();
		for (int i = 0; i <= r; i++) {
			final long position = indexer.getIdx(fp0, i);
			final long l = array.get(position);
			if (fp0 == (l & FLUSHED_MASK)) {
				// zero the long msb (which is 1 if fp has been flushed to disk)
				return true;
			} else 	if (l == EMPTY) {
				return false;
			}
		}

		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#memInsert(long)
	 */
	final boolean memInsert(final long fp0) throws IOException {
		for (int i = 0; i < PROBE_LIMIT; i++) {
			final long position = indexer.getIdx(fp0, i);
			final long expected = array.get(position);
			if (expected == EMPTY || (expected < 0 && fp0 != (expected & FLUSHED_MASK))) {
				// Increment reprobe if needed. Other threads might have
				// increased concurrently. Since reprobe is strictly
				// monotonic increasing, we need no retry when r larger.
				reprobe.accumulate(i);
				
				// Try to CAS the new fingerprint. In case of failure, reprobe
				// is too large which we ignore. Will be eventually corrected
				// by eviction.
				if (array.trySet(position, expected, fp0)) {
					this.tblCnt.increment();
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
				this.memHitCnt.increment();
				return true;
			}
			
			// Lookup on disk
			if (this.diskLookup(fp0)) {
				this.diskHitCnt.increment();
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
			diskHitCnt.increment();
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
			final long buffLen = tblCnt.sum();
			final Iterator itr = new Iterator(array, buffLen, indexer);

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
	public static class Iterator {
		private final long elements;
		private final LongArray array;
		private final Indexer indexer;

		private long pos = 0;
		private long elementsRead = 0L;
		
		public Iterator(final LongArray array, final long elements, final Indexer indexer) {
			this.array = array;
			this.elements = elements;
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
			long elem = EMPTY;
			do {
				long position = pos % array.size();
				elem = array.get(position);
				pos = pos + 1L;
				if (elem <= EMPTY) {
					continue;
				}
				final long baseIdx = indexer.getIdx(elem);
				if (baseIdx > pos) {
					continue;
				}
				// mark elem in array as being evicted.
				array.set(position, elem | MARK_FLUSHED);
				elementsRead = elementsRead + 1L;
				return elem;
			} while (hasNext());
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
			return elementsRead < elements;
		}
	}
}
