// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.concurrent.BrokenBarrierException;
import java.util.concurrent.Callable;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.LongAccumulator;
import java.util.function.LongBinaryOperator;
import java.util.function.ToLongFunction;
import java.util.logging.Level;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.LongArrays.LongComparator;
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
	
	/**
	 * completionException is set by the Runnable iff an exception occurs during
	 * eviction while the worker threads wait at barrier. Worker threads have to
	 * check completionException explicitly.
	 */
	private volatile RuntimeException completionException;

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
		
		// Use the non-concurrent flusher as the default. Will be replaced by
		// the CyclicBarrier-Runnable later. Just set to prevent NPEs when
		// eviction/flush is called before init.
		this.flusher = new OffHeapMSBFlusher(array, 0);
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
					OffHeapDiskFPSet.this.flusher = new ConcurrentOffHeapMSBFlusher(array, r, numThreads, insertions);
				} else {
					OffHeapDiskFPSet.this.flusher = new OffHeapMSBFlusher(array, r);
				}
				
				try {
					flusher.flushTable(); // Evict()
				} catch (RuntimeException e) {
					completionException = e;
					throw e;
				} catch (IOException e) {
					completionException = new RuntimeException(e);
					throw completionException;
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
				Assert.check(flusherChosen.compareAndSet(true, false), EC.GENERAL);
			}
		});
	}
	
	private boolean checkEvictPending() {
		if (flusherChosen.get()) {
			try {
				barrier.await();
				if (completionException != null) {
					throw completionException;
				}
			} catch (InterruptedException ie) {
				throw new RuntimeException(ie);
			} catch (BrokenBarrierException bbe) {
				barrier.reset();
				if (completionException != null) {
					throw completionException;
				} else { 
					throw new RuntimeException(bbe);
				}
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
			} else if (l == EMPTY) {
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
		if (this.diskLookup(fp0)) {
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
			assert fpBits > 0;
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

	/**
	 * Returns the number of fingerprints stored in table/array in the range
	 * [start,limit].
	 */
	private long getTableOffset(final LongArray a, final long reprobe, final Indexer indexer, final long start,
			final long limit) {
		long occupied = 0L;
		for (long pos = start; pos < limit; pos++) {
			final long fp = a.get(pos % a.size());
			if (fp <= EMPTY) {
				continue;
			}
			final long idx = indexer.getIdx(fp);
			if (idx > pos) {
				// Ignore the elements that wrapped around the
				// end when scanning the first partition.
				continue;
			}
			if (idx + reprobe < pos) {
				// Ignore the elements of the first partition
				// when wrapping around for the last partition.
				continue;
			}
			occupied = occupied + 1L;
		}
		return occupied;
	}
	
	private long getNextLower(long idx) {
		// Reverse to the next non-evicted/empty fp that belongs to this partition.
		long fp = array.get(idx);
		while (fp <= EMPTY || indexer.getIdx(fp) > idx) {
			fp = array.get(--idx);
		}
		return fp;
	}
	
	/**
	 * The number of fingerprints stored on disk smaller than fp.
	 */
	private long getDiskOffset(final int id, final long fp) throws IOException {
		if (this.index == null) {
			return 0L;
		}
		
		final int indexLength = this.index.length;
		int loPage = 0, hiPage = indexLength - 1;
		long loVal = this.index[loPage];
		long hiVal = this.index[hiPage];

		if (fp <= loVal) {
			return 0L;
		}
		if (fp >= hiVal) {
			return this.braf[id].length() / FPSet.LongSize;
		}
		// See DiskFPSet#diskLookup for comments.
		
		// Lookup the corresponding disk page in index.
		final double dfp = (double) fp;
		while (loPage < hiPage - 1) {
			final double dhi = (double) hiPage;
			final double dlo = (double) loPage;
			final double dhiVal = (double) hiVal;
			final double dloVal = (double) loVal;
			int midPage = (loPage + 1) + (int) ((dhi - dlo - 1.0) * (dfp - dloVal) / (dhiVal - dloVal));
			if (midPage == hiPage) {
				midPage--;
			}
			final long v = this.index[midPage];
			if (fp < v) {
				hiPage = midPage;
				hiVal = v;
			} else if (fp > v) {
				loPage = midPage;
				loVal = v;
			} else {
				return (midPage * 1L) * (NumEntriesPerPage * 1L);
			}
		}
		// no page is in between loPage and hiPage at this point
		Assert.check(hiPage == loPage + 1, EC.SYSTEM_INDEX_ERROR);

		// Read the disk page and try to find the given fingerprint or the next
		// smaller one. Calculate its offset in file.
		long midEntry = -1L;
		long loEntry = ((long) loPage) * NumEntriesPerPage;
		long hiEntry = ((loPage == indexLength - 2) ? this.fileCnt - 1 : ((long) hiPage) * NumEntriesPerPage);
		final BufferedRandomAccessFile raf = this.braf[id];
		while (loEntry < hiEntry) {
			midEntry = calculateMidEntry(loVal, hiVal, dfp, loEntry, hiEntry);
			raf.seek(midEntry * LongSize);
			final long v = raf.readLong();

			if (fp < v) {
				hiEntry = midEntry;
				hiVal = v;
			} else if (fp > v) {
				loEntry = midEntry + 1;
				loVal = v;
				midEntry = loEntry;
			} else {
				break;
			}
		}
		return midEntry;
	}
	
	public class ConcurrentOffHeapMSBFlusher extends OffHeapMSBFlusher {
		
		private final int numThreads;
		private final ExecutorService executorService;
		private final long insertions;
		/**
		 * The length of a single partition.
		 */
		private final long length;
		private List<Future<Result>> offsets; 

		public ConcurrentOffHeapMSBFlusher(final LongArray array, final int r, final int numThreads,
				final long insertions) {
			super(array, r);
			this.numThreads = numThreads;
			this.insertions = insertions;

			this.length = (long) Math.floor(a.size() / numThreads);
			this.executorService = Executors.newFixedThreadPool(numThreads);
		}
		
		/* (non-Javadoc)
		 * @see tlc2.tool.fp.DiskFPSet.Flusher#prepareTable()
		 */
		protected void prepareTable() {
			final CyclicBarrier phase = new CyclicBarrier(this.numThreads);
			final Collection<Callable<Result>> tasks = new ArrayList<Callable<Result>>(numThreads);
			for (int i = 0; i < numThreads; i++) {
				final int id = i;
				tasks.add(new Callable<Result>() {
					@Override
					public Result call() throws Exception {
						final boolean isFirst = id == 0;
						final boolean isLast = id == numThreads - 1;
						final long start = id * length;
						final long end = isLast ? a.size() - 1L : start + length;
						
						// Sort partition p_n. We have exclusive access.
						LongArrays.sort(a, start, end, getLongComparator());
						
						// Wait for the other threads sorting p_n+1 to be done
						// before we stitch together p_n and p_n+1.
						phase.await();

						// Sort the range between partition p_n and
						// p_n+1 bounded by reprobe.
						LongArrays.sort(a, end - r+1L, end + r+1L, getLongComparator());
						
						// Wait for table to be fully sorted before we calculate
						// the offsets. Offsets can only be correctly calculated
						// on a sorted table.
						phase.await();
						
						// Count the occupied positions for this
						// partition. Occupied positions are those which
						// get evicted (written to disk).
						// This could be done as part of (insertion) sort
						// above at the price of higher complexity. Thus,
						// it's done here until it becomes a bottleneck.
						final long limit = isLast ? a.size() + r : end;
						long occupied = getTableOffset(a, r, indexer, start, limit);
						
						if (index == null) {
							// No index, no need to calculate a disk offset.
							return new Result(occupied, 0L);
						}
						
						// Determine number of elements in the old/current file.
						if (isFirst && isLast) {
							return new Result(occupied, fileCnt);
						} else if (isFirst) {
							return new Result(occupied, getDiskOffset(id, getNextLower(end)));
						} else if (isLast) {
							return new Result(occupied, fileCnt - getDiskOffset(id, getNextLower(start)));
						} else {
							return new Result(occupied,
									getDiskOffset(id, getNextLower(end)) - getDiskOffset(id, getNextLower(start)));
						}
					}
				});
			}
			try {
				offsets = executorService.invokeAll(tasks);
			} catch (InterruptedException ie) {
				throw new RuntimeException(ie);
			}

			assert checkSorted(a, indexer, r) == -1L : String.format(
					"Array %s not fully sorted at index %s and reprobe %s.", a.toString(),
					checkSorted(array, indexer, r), r);
		}

		@Override
		protected void mergeNewEntries(final RandomAccessFile[] inRAFs, final RandomAccessFile outRAF, final Iterator ignored, final int idx, final long cnt) throws IOException {
			assert offsets.stream().mapToLong(new ToLongFunction<Future<Result>>() {
				public long applyAsLong(Future<Result> future) {
					try {
						return future.get().getTable();
					} catch (InterruptedException ie) {
						throw new RuntimeException(ie);
					} catch (ExecutionException ee) {
						throw new RuntimeException(ee);
					}
				}
			}).sum() == insertions : "Missing inserted elements during eviction.";
			assert offsets.stream().mapToLong(new ToLongFunction<Future<Result>>() {
				public long applyAsLong(Future<Result> future) {
					try {
						return future.get().getDisk();
					} catch (InterruptedException ie) {
						throw new RuntimeException(ie);
					} catch (ExecutionException ee) {
						throw new RuntimeException(ee);
					}
				}
			}).sum() == fileCnt : "Missing disk elements during eviction.";
			final Collection<Callable<Void>> tasks = new ArrayList<Callable<Void>>(numThreads);
			// Id = 0
			tasks.add(new Callable<Void>() {
				public Void call() throws Exception {
					final Result result = offsets.get(0).get();
					final Iterator itr = new Iterator(a, result.getTable(), indexer);
					ConcurrentOffHeapMSBFlusher.super.mergeNewEntries(inRAFs[0], outRAF, itr, 0, 0L, result.getDisk());
					assert outRAF.getFilePointer() == result.getTotal()
							* FPSet.LongSize : "First writer did not write expected amount of fingerprints to disk.";
					return null;
				}
			});
			// Id > 0
			for (int i = 1; i < numThreads; i++) {
				final int id = i;
				tasks.add(new Callable<Void>() {
					public Void call() throws Exception {
						final RandomAccessFile tmpRAF = new BufferedRandomAccessFile(new File(tmpFilename), "rw");
						tmpRAF.setLength(outRAF.length());
						try {
							// Sum up the combined number of elements in
							// lower partitions.
							long skipOutFile = 0L;
							long skipInFile = 0L;
							for (int j = 0; j < id; j++) {
								skipInFile = skipInFile + offsets.get(j).get().getDisk();
								skipOutFile = skipOutFile + offsets.get(j).get().getTotal();
							}

							// Set offsets into the out (tmp) file.
							final Result result = offsets.get(id).get();
							tmpRAF.seek(skipOutFile * FPSet.LongSize);

							// Set offset and the number of elements the
							// iterator is supposed to return.
							final long table = result.getTable();
							final Iterator itr = new Iterator(a, table, id * length, indexer);
							final RandomAccessFile inRAF = inRAFs[id];
							assert (skipInFile + result.getDisk()) * FPSet.LongSize <= inRAF.length();
							inRAF.seek(skipInFile * FPSet.LongSize);

							// Calculate where the index entries start and end.
							final int idx = (int) Math.floor(skipOutFile / NumEntriesPerPage);
							final long cnt = NumEntriesPerPage - (skipOutFile - (idx * NumEntriesPerPage));

							// Stop reading after diskReads elements (after
							// which the next thread continues) except for the
							// last thread which reads until EOF. Pass 0 when
							// nothing can be read from disk.
							final long diskReads = id == numThreads - 1 ? fileCnt - skipInFile : result.getDisk();
							
							ConcurrentOffHeapMSBFlusher.super.mergeNewEntries(inRAF, tmpRAF, itr, idx + 1, cnt, diskReads);

							assert tmpRAF.getFilePointer() == (skipOutFile + result.getTotal()) * FPSet.LongSize : id
									+ " writer did not write expected amount of fingerprints to disk.";
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
			} catch (InterruptedException ie) {
				throw new RuntimeException(ie);
			} finally {
				executorService.shutdown();
			}

			assert checkTable(a) : "Missed element during eviction.";
			assert checkIndex(index) : "Inconsistent disk index.";
		}

		private class Result {
			private final long occupiedTable;
			private final long occupiedDisk;
			
			public Result(long occupiedTable, long occupiedDisk) {
				this.occupiedTable = occupiedTable;
				this.occupiedDisk = occupiedDisk;
			}
			public long getDisk() {
				return occupiedDisk;
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

			// maintain object invariants
			fileCnt += buffLen;
		}

		protected void mergeNewEntries(RandomAccessFile[] inRAFs, RandomAccessFile outRAF, Iterator itr, int currIndex,
				long counter) throws IOException {
			inRAFs[0].seek(0);
			mergeNewEntries(inRAFs[0], outRAF, itr, currIndex, counter, inRAFs[0].length() / FPSet.LongSize);
		}

		protected void mergeNewEntries(RandomAccessFile inRAF, RandomAccessFile outRAF, final Iterator itr,
				int currIndex, long counter, long diskReads) throws IOException {
			
			final int startIndex = currIndex;
			
			// initialize positions in "buff" and "inRAF"
			long value = 0L; // initialize only to make compiler happy
			boolean eof = false;
			if (fileCnt > 0) {
				try {
					value = inRAF.readLong();
					diskReads--;
				} catch (EOFException e) {
					eof = true;
				}
			} else {
				assert diskReads == 0L;
				eof = true;
			}

			// merge while both lists still have elements remaining
			boolean eol = false;
			long fp = itr.next();
			while (!eof || !eol) {
				if ((value < fp || eol) && !eof) {
					assert value > EMPTY : "Negative or zero fingerprint found: " + value;
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
						if (diskReads-- == 0L) {
							eof = true;
						}
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
					assert fp > EMPTY : "Wrote an invalid fingerprint to disk.";
					outRAF.writeLong(fp);
					diskWriteCnt.increment();
					// update in-memory index file
					if (counter == 0) {
						index[currIndex++] = fp;
						counter = NumEntriesPerPage;
					}
					counter--;
					// we used one fp up, thus move to next one
					if (itr.hasNext()) {
						fp = itr.next();
					} else {
						eol = true;
					}
				}
			}
			// both sets used up completely
			Assert.check(eof && eol, EC.GENERAL);
			
			if (currIndex == index.length - 1) {
				// Update the last element in index with the larger one of the
				// current largest element of itr and the largest element of value.
				index[index.length - 1] = Math.max(fp, value);
			} else if (counter == 0) {
				// Write the last index entry if counter reached zero in the
				// while loop above.
				index[currIndex] = Math.max(fp, value);
			}
			
			assert checkIndex(Arrays.copyOfRange(index, startIndex, currIndex)) : "Inconsistent disk index range.";
		}
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#calculateIndexLen(long)
	 */
	protected int calculateIndexLen(final long tblcnt) {
		int indexLen = super.calculateIndexLen(tblcnt);
		if ((tblcnt + fileCnt - 1L) % NumEntriesPerPage == 0L) {
			// This is the special case where the largest fingerprint
			// happened is going to end up on the last entry of the previous
			// page. Thus, we won't need the last extra index cell.
			indexLen--;
		}
		return indexLen;
	}
	
	/**
	 * A non-thread safe Iterator whose next method returns the next largest
	 * element.
	 */
	public static class Iterator {

		private enum WRAP {
			ALLOWED, FORBIDDEN;
		};

		private final long elements;
		private final LongArray array;
		private final Indexer indexer;
		private final WRAP canWrap;

		private long pos = 0;
		private long elementsRead = 0L;
		
		public Iterator(final LongArray array, final long elements, final Indexer indexer) {
			this(array, elements, 0L, indexer, WRAP.ALLOWED);
		}

		public Iterator(final LongArray array, final long elements, final long start, final Indexer indexer) {
			this(array, elements, start, indexer, WRAP.FORBIDDEN);
		}

		public Iterator(final LongArray array, final long elements, final long start, final Indexer indexer,
				final WRAP canWrap) {
			this.array = array;
			this.elements = elements;
			this.indexer = indexer;
			this.pos = start;
			this.canWrap = canWrap;
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
				final long position = pos % array.size();
				elem = array.get(position);
				if (elem == EMPTY) {
					pos = pos + 1L;
					continue;
				}
				if (elem < EMPTY) {
					pos = pos + 1L;
					continue;
				}
				final long baseIdx = indexer.getIdx(elem);
				if (baseIdx > pos) {
					// This branch should only be active for thread with id 0.
					assert canWrap == WRAP.ALLOWED;
					pos = pos + 1L;
					continue;
				}
				pos = pos + 1L;
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

	// ***************** assertion helpers *******************//

	/**
	 * @return -1L iff array is sorted, index/position of the element that violates otherwise.
	 */
	private static long checkSorted(final LongArray array, final Indexer indexer, final int reprobe) {
		long e = 0L;
		for (long pos = 0L; pos < array.size() + reprobe; pos++) {
			final long tmp = array.get(pos % array.size());
			if (tmp <= EMPTY) {
				continue;
			}
			final long idx = indexer.getIdx(tmp);
			if (idx > pos) {
				continue;
			}
			if (idx + reprobe < pos) {
				continue;
			}
			if (e == 0L) {
				// Initialize e with the first element that is not <=EMPTY
				// or has wrapped.
				e = tmp;
				continue;
			}
			if (e >= tmp) {
				return pos;
			}
			e = tmp;
		}
		return -1L;
	}

	private static boolean checkTable(LongArray array) {
		for (long i = 0L; i < array.size(); i++) {
			long elem = array.get(i);
			if (elem > EMPTY) {
				return false;
			}
		}
		return true;
	}

	private static boolean checkIndex(final long[] idx) {
		for (int i = 1; i < idx.length; i++) {
			if (idx[i - 1] >= idx[i]) {
				return false;
			}
		}
		return true;
	}
}
