// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.concurrent.BrokenBarrierException;
import java.util.concurrent.Callable;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.LongAccumulator;
import java.util.function.LongBinaryOperator;
import java.util.logging.Level;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.LongArrays.LongComparator;
import tlc2.tool.fp.OffHeapDiskFPSet2.Iterator;
import tlc2.tool.fp.management.DiskFPSetMXWrapper;
import tlc2.util.BufferedRandomAccessFile;
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
				
				// Only pay the price of creating threads when array is sufficiently large.
				if (array.size() > 8192) {
					OffHeapDiskFPSet.this.flusher = new ConcurrentOffHeapMSBFlusher(array, r, numThreads);
				} else {
					OffHeapDiskFPSet.this.flusher = new OffHeapMSBFlusher(array, r);
				}
				
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

	// Returns the number of fingerprints stored in the current file
	private long getOffset(final long fp) {
		if (this.index == null) {
			return 0L;
		}
		//TODO
		throw new UnsupportedOperationException("Not yet implemented");
	}
	
	public class ConcurrentOffHeapMSBFlusher extends OffHeapMSBFlusher {
		
		private final int numThreads;
		private final ExecutorService executorService;
		private final Striped striped;
		/**
		 * The length of a single partition.
		 */
		private final long length;
		private List<Future<Result>> offsets; 

		public ConcurrentOffHeapMSBFlusher(final LongArray array, final int r, final int numThreads) {
			super(array, r);
			this.numThreads = numThreads;
			
			this.length = (long) Math.floor(a.size() / numThreads);
			this.striped = Striped.readWriteLock(numThreads);
			this.executorService = Executors.newFixedThreadPool(numThreads);
		}
		
		/* (non-Javadoc)
		 * @see tlc2.tool.fp.DiskFPSet.Flusher#prepareTable()
		 */
		protected void prepareTable() {
			final Collection<Callable<Result>> tasks = new ArrayList<Callable<Result>>(numThreads);
			for (int i = 0; i < numThreads; i++) {
				final int id = i;
				tasks.add(new Callable<Result>() {
					@Override
					public Result call() throws Exception {
						final long start = id * length;
						final long end = id == numThreads - 1 ? a.size() - 1L : start + length - 1L;
						
						// Sort partition p_n while holding its
						// corresponding lock. Sort requires exclusive
						// access.
						striped.getAt(id).writeLock().lock();
						LongArrays.sort(a, start, end, getLongComparator());
						striped.getAt(id).writeLock().unlock();
						
						// Sort the range between partition p_n and
						// p_n+1 bounded by reprobe. We need no hold
						// lock for p_n because p_n is done (except for
						// its non-overlapping lower end).
						striped.getAt((id + 1) % numThreads).writeLock().lock();
						LongArrays.sort(a, end - r, end + r, getLongComparator());
						striped.getAt((id + 1) % numThreads).writeLock().unlock();
						
						// Count the occupied positions for this
						// partition. Occupied positions are those which
						// get evicted (written to disk).
						// This could be done as part of (insertion) sort
						// above at the price of higher complexity. Thus,
						// it's done here until it becomes a bottleneck.
						long occupied = 0L;
						for (long pos = start; pos < end; pos++) {
							if (a.get(pos) <= EMPTY || indexer.getIdx(a.get(pos)) > pos) {
								continue;
							}
							occupied = occupied + 1;
						}
						
						// Determine number of elements in the old/current file.
						long occupiedFile = getOffset(a.get(start));
						
						return new Result(occupied, occupiedFile);
					}
				});
			}
			try {
				offsets = executorService.invokeAll(tasks);
			} catch (InterruptedException notExpectedToHappen) {
				notExpectedToHappen.printStackTrace();
			}
			
			//TODO Remove check everything is sorted.
			long e = a.get(0);
			for(long i = 1; i < a.size(); i++) {
				if (a.get(i) <= EMPTY || indexer.getIdx(a.get(i)) > i) {
					continue;
				}
				if (e >= a.get(i)) {
					Assert.fail(EC.SYSTEM_INDEX_ERROR, String.format("%s >= %s", e, a.get(i)));
				}
				e = a.get(i);
			}
		}

		@Override
		protected void mergeNewEntries(final RandomAccessFile[] inRAFs, final RandomAccessFile outRAF, final Iterator ignored, final int idx, final long cnt) throws IOException {
			// Make assert in caller method happy
			currIndex = calculateIndexLen(tblCnt.sum()) - 1;
			
			final Collection<Callable<Void>> tasks = new ArrayList<Callable<Void>>(numThreads);
			// Id = 0
			tasks.add(new Callable<Void>() {
				public Void call() throws Exception {
					final Iterator itr = new Iterator(a, offsets.get(0).get().getTable(), indexer);
					ConcurrentOffHeapMSBFlusher.super.mergeNewEntries(inRAFs[0], outRAF, itr, 0, 0L);
					return null;
				}
			});
			// Id > 0
			for (int i = 1; i < numThreads; i++) {
				final int id = i;
				tasks.add(new Callable<Void>() {
					public Void call() throws Exception {
						final RandomAccessFile tmpRAF = new BufferedRandomAccessFile(new File(tmpFilename), "rw");
						try {
							// Sum up the combined number of elements in
							// lower partitions.
							long skipTotal = 0L;
							for (int j = 0; j < id; j++) {
								skipTotal = skipTotal + offsets.get(j).get().getTotal();
							}

							final Result result = offsets.get(id).get();
							tmpRAF.setLength((skipTotal + result.getTotal()) * FPSet.LongSize);
							tmpRAF.seek(skipTotal * FPSet.LongSize);

							final long table = result.getTable();
							final Iterator itr = new Iterator(a, table, id * length, indexer);

							final RandomAccessFile inRAF = inRAFs[id];

							final int idx = (int) Math.floor(skipTotal / NumEntriesPerPage);
							final long cnt = NumEntriesPerPage - (skipTotal - (idx * NumEntriesPerPage));
							ConcurrentOffHeapMSBFlusher.super.mergeNewEntries(inRAF, tmpRAF, itr, idx + 1, cnt);
						} finally {
							tmpRAF.close();
						}
						return null;
					}
				});
			}
			// Combine the callable results.
			try {
				executorService.invokeAll(tasks);
			} catch (InterruptedException notExpectedToHappen) {
				notExpectedToHappen.printStackTrace();
			} finally {
				executorService.shutdown();
			}
			
			//TODO Remove check
			for (int i = 1; i < index.length; i++) {
				if(index[i-1] >= index[i]) {
					Assert.fail(EC.SYSTEM_INDEX_ERROR, String.format("%s >= %s", index[i-1], index[i]));
				}
			}
		}
		
		private class Result {
			private final long occupiedTable;
			private final long occupiedDisk;
			
			public Result(long occupiedTable, long occupiedDisk) {
				this.occupiedTable = occupiedTable;
				this.occupiedDisk = occupiedDisk;
			}
			public long getTable() {
				return occupiedTable;
			}
			public long getTotal() {
				return occupiedDisk + occupiedTable;
			}
		}
	}
	
	public class OffHeapMSBFlusher extends Flusher {
		
		protected final int r;
		protected final LongArray a;

		public OffHeapMSBFlusher(LongArray array, int reprobe) {
			a = array;
			r = reprobe;
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.DiskFPSet.Flusher#prepareTable()
		 */
		protected void prepareTable() {
			super.prepareTable();
			// Sort with a single thread.
			LongArrays.sort(a, 0, a.size() - 1L + r, getLongComparator());
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.MSBDiskFPSet#mergeNewEntries(java.io.RandomAccessFile, java.io.RandomAccessFile)
		 */
		@Override
		protected void mergeNewEntries(RandomAccessFile[] inRAFs, RandomAccessFile outRAF) throws IOException {
			final long buffLen = tblCnt.sum();
			final Iterator itr = new Iterator(array, buffLen, indexer);

			final int indexLen = calculateIndexLen(buffLen);
			index = new long[indexLen];
			mergeNewEntries(inRAFs, outRAF, itr, 0, 0L);

			// currIndex is amount of disk writes
			Assert.check(currIndex == indexLen - 1, EC.SYSTEM_INDEX_ERROR);

			// maintain object invariants
			fileCnt += buffLen;
		}

		protected void mergeNewEntries(RandomAccessFile[] inRAFs, RandomAccessFile outRAF, Iterator itr, int currIndex,
				long counter) throws IOException {
			inRAFs[0].seek(0);
			mergeNewEntries(inRAFs[0], outRAF, itr, currIndex, counter);
		}

		protected void mergeNewEntries(RandomAccessFile inRAF, RandomAccessFile outRAF, final Iterator itr, final int idx, final long cnt) throws IOException {
			int currIndex = idx;
			long counter = cnt;

			// initialize positions in "buff" and "inRAF"
			long value = 0L; // initialize only to make compiler happy
			boolean eof = false;
			if (fileCnt > 0) {
				try {
					value = inRAF.readLong();
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
					outRAF.writeLong(value);
					diskWriteCnt.increment();
					// update in-memory index file
					if (counter == 0) {
						index[currIndex++] = value;
						counter = NumEntriesPerPage;
					}
					counter--;
					try {
						value = inRAF.readLong();
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
					outRAF.writeLong(fp);
					diskWriteCnt.increment();
					// update in-memory index file
					if (counter == 0) {
						index[currIndex++] = fp;
						counter = NumEntriesPerPage;
					}
					counter--;
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
			
			if (currIndex == index.length - 1) {
				// Update the last element in index with the large one of the
				// current largest element of itr and the previous largest element.
				index[index.length - 1] = fp;
			}
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
			this(array, elements, 0L, indexer);
		}
		
		public Iterator(final LongArray array, final long elements, final long start, final Indexer indexer) {
			this.array = array;
			this.elements = elements;
			this.indexer = indexer;
			this.pos = start;
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
