// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CyclicBarrier;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.Phaser;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.ToLongFunction;
import java.util.logging.Level;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.LongArrays.LongComparator;
import tlc2.tool.fp.management.DiskFPSetMXWrapper;
import tlc2.util.BufferedRandomAccessFile;
import util.Assert;

/**
 * see OpenAddressing.tla
 */
@SuppressWarnings({ "serial" })
public final class OffHeapDiskFPSet extends NonCheckpointableDiskFPSet implements FPSetStatistic {
	
	private static class OffHeapSynchronizer {
		
		private final Set<OffHeapDiskFPSet> sets = new HashSet<OffHeapDiskFPSet>();
		
		private final AtomicBoolean flusherChosen = new AtomicBoolean();
		
		// This barrier gets run after one thread signals the need to suspend
		// put and contains operations to evict to secondary. Signaling is done
		// via the flusherChoosen AtomicBoolean. All threads (numThreads) will
		// then await on the barrier and the Runnable be executed when the
		// last of numThreads arrives.
		// Compared to an AtomicBoolean, the barrier operation use locks and
		// are thus comparably expensive.
		private final Phaser phaser = new Phaser(1) {

			@Override
			protected boolean onAdvance(int phase, int registeredParties) {
				// Atomically evict and reset flusherChosen to make sure no
				// thread re-read flusherChosen=true after an eviction and
				// waits again.
				for (OffHeapDiskFPSet set : sets) {
					set.evict();
				}

				// Release exclusive access. It has to be done by the runnable
				// before workers waiting on the barrier wake up again.
				Assert.check(flusherChosen.compareAndSet(true, false), EC.GENERAL);
				
				return super.onAdvance(phase, registeredParties);
			}
		};
		
		private OffHeapSynchronizer() {
			// Don't want any copies.
		}
		
		public final void add(final OffHeapDiskFPSet aSet) {
			this.sets.add(aSet);
		}
		
		public final void incWorkers(final int numWorkers) {
			final int parties = phaser.getRegisteredParties();
			if (parties < numWorkers) {
				phaser.bulkRegister(numWorkers - parties);
			}
		}
		
		public final boolean evictPending() {
			return flusherChosen.get();
		}
		
		public final void evict() {
			flusherChosen.compareAndSet(false, true);
		}
		
		public final void awaitEviction() {
			phaser.arriveAndAwaitAdvance();
		}
		
		public AtomicBoolean getFlusherChosen() {
			return flusherChosen;
		}
	}

	// We require a singleton here, because if TLC is run with multiple instances
	// of FPSets - the default - workers will call evict and awaitEvict on 
	// all FPSet instances. Thus, an individual synchronization internal to each
	// FPSet would never see the complete set of waiting workers. TLC would thus
	// deadlock. This is why SYNC is a singleton and shared by all FPSet instances.
	private static final OffHeapSynchronizer SYNC = new OffHeapSynchronizer();
	
	private static final int PROBE_LIMIT = Integer.getInteger(OffHeapDiskFPSet.class.getName() + ".probeLimit", 1024);
	static final long EMPTY = 0L;
	

	/**
	 * @see LongArray#isSupported()
	 */
	public static boolean isSupported() {
		return LongArray.isSupported();
	}

	private final transient LongArray array;
	
	/**
	 * The indexer maps a fingerprint to a in-memory bucket and the associated lock
	 */
	private final transient Indexer indexer;

	private int numThreads;

	protected OffHeapDiskFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
		super(fpSetConfig);
		
		final long positions = fpSetConfig.getMemoryInFingerprintCnt();
		
		// Determine base address which varies depending on machine architecture.
		this.array = new LongArray(positions);
		
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
		this.flusher = new OffHeapMSBFlusher(array);
		
		this.flusherChosen = SYNC.getFlusherChosen();
		SYNC.add(this);
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#init(int, java.lang.String, java.lang.String)
	 */
	@Override
	public FPSet init(final int numThreads, String aMetadir, String filename)
			throws IOException {
		super.init(numThreads, aMetadir, filename);
		this.numThreads = numThreads;
		
		array.zeroMemory(numThreads);
		return this;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#incWorkers(int)
	 */
	public void incWorkers(int numWorkers) {
		assert numWorkers == this.numThreads;
		SYNC.incWorkers(numWorkers);
	}

	public void evict() {
		// statistics
		growDiskMark++;
		final long timestamp = System.currentTimeMillis();
		final long insertions = tblCnt.longValue();
		final double lf = tblCnt.doubleValue() / (double) maxTblCnt;
		
		LOGGER.log(Level.FINE,
				"Started eviction of disk {0} the {1}. time at {2} after {3} insertions, load factor {4} and reprobe of {5}.",
				new Object[] { ((DiskFPSetMXWrapper) diskFPSetMXWrapper).getObjectName(), getGrowDiskMark(),
						timestamp, insertions, lf, PROBE_LIMIT });
		
		// Check that the table adheres to our invariant. Otherwise, we
		// can't hope to successfully evict it.
		assert checkInput(array, indexer, PROBE_LIMIT) : "Table violates invariants prior to eviction: "
				+ array.toString();
		
		// Only pay the price of creating threads when array is
		// sufficiently large and the array size is large enough to
		// partition it for multiple threads.
		flusher = getFlusher(numThreads, insertions);
		
		try {
			flusher.flushTable(); // Evict()
		} catch (IOException e) {
			// wrap in unchecked.
			throw new OffHeapRuntimeException(e);
		}

		// statistics and logging again.
		final long l = System.currentTimeMillis() - timestamp;
		flushTime += l;
		LOGGER.log(Level.FINE,
				"Finished eviction of disk {0} the {1}. time at {2}, in {3} sec after {4} insertions, load factor {5} and reprobe of {6}.",
				new Object[] { ((DiskFPSetMXWrapper) diskFPSetMXWrapper).getObjectName(), getGrowDiskMark(), l,
						System.currentTimeMillis(), insertions, lf, PROBE_LIMIT });
	}

	private Flusher getFlusher(final int numThreads, final long insertions) {
		if (array.size() >= 8192 && Math.floor(array.size() / (double) numThreads) > 2 * PROBE_LIMIT) {
			return new ConcurrentOffHeapMSBFlusher(array, PROBE_LIMIT, numThreads, insertions);
		} else {
			return this.flusher;
		}
	}

	private boolean checkEvictPending() {
		if (SYNC.evictPending()) {
			SYNC.awaitEviction();
			return true;
		}
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#sizeof()
	 */
	public long sizeof() {
		long size = 44; // approx size of this DiskFPSet object
		size += maxTblCnt * LongSize;
		size += getIndexCapacity() * 4;
		return size;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#needsDiskFlush()
	 */
	@Override
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
    
	private static final int FOUND = -1;
    
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#memLookup(long)
	 */
	final boolean memLookup(final long fp0) {
		return memLookup0(fp0) == FOUND;
	}

	final int memLookup0(final long fp0) {
		int free = PROBE_LIMIT;
		for (int i = 0; i <= PROBE_LIMIT; i++) {
			final long position = indexer.getIdx(fp0, i);
			final long l = array.get(position);
			if (fp0 == (l & FLUSHED_MASK)) {
				// zero the long msb (which is 1 if fp has been flushed to disk)
				return FOUND;
			} else if (l == EMPTY) {
				return Math.min(i, free);
			} else if (l < EMPTY && free == PROBE_LIMIT) {
				free = i;
			}
		}

		return free;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#memInsert(long)
	 */
	final boolean memInsert(final long fp0) throws IOException {
		return memInsert0(fp0, 0);
	}

	final boolean memInsert0(final long fp0, final int start) throws IOException {
		// See OffHeapDiskFPSetJPFTest for a (verbatim) version that has
		// additionally been verified with JPF.
		for (int i = start; i < PROBE_LIMIT; i++) {
			final long position = indexer.getIdx(fp0, i);
			final long expected = array.get(position);
			if (expected == EMPTY || (expected < 0 && fp0 != (expected & FLUSHED_MASK))) {
				// Try to CAS the new fingerprint.
				if (array.trySet(position, expected, fp0)) {
					this.tblCnt.increment();
					return false;
				} else {
					// Retry at current position because another thread wrote a
					// value concurrently (possibly the same one this thread is
					// trying to write).
					i = i - 1;
					continue;
				}
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
		if (checkEvictPending()) {
			return put(fp);
		}

		// zeros the msb
		final long fp0 = fp & FLUSHED_MASK;

		// Only check primary and disk iff there exists a disk file. index is
		// created when we wait and thus cannot race.
		int start = 0;
		if (index != null) {
			// Lookup primary memory
			if ((start = memLookup0(fp0)) == FOUND) {
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
		return memInsert0(fp0, start);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#contains(long)
	 */
	public final boolean contains(final long fp) throws IOException {
		// maintains happen-before with regards to successful put
		
		if (checkEvictPending()) {
			return contains(fp);
		}

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
		SYNC.evict();
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
		return PROBE_LIMIT;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#checkFPs()
	 */
	@Override
	public long checkFPs() throws IOException {
		if (getTblCnt() <= 0) {
			return Long.MAX_VALUE;
		}
		// The superclass implementation provides insufficient performance and
		// scalability. These problems get more pronounced with large arrays.
		// In order to provide a faster solution to the closest pair problem in
		// one-dimensional space, we cheat and determine the minimum distance
		// between fingerprints only on a subset of fingerprints. The subset are
		// those fingerprints which happen to be in main memory and have not yet
		// been evicted to disk. We believe this to be a sufficient approximation.
		// The algorithm to find the closest pair in one-dimensional space is:
		// 1) Sort all fingerprints.
		// 2) Perform a linear scan/search
		// => O(n log n)
		// Scalability is achieved by partitioning the array for 1) and 2),
		// which is possible due to the bounded disorder in array.
		
		// One can think of two shortcuts to approximate of the closest pair:
		// a) Track the minimum distance during the 1) step in prepareTable. A possible
		// implementation can pass something similar to a BinaryOpeartor to the
		// LongComparator. Due to the bounded disorder, this generally works except for
		// the corner case where the closest pair are two fingerprints in two
		// non-adjacent partitions, i.e. [,,,fp23],[],...,[],[,,fp42,,,]. This is
		// frequently the case for very sparsely populated arrays. 
		// b) For low load factors (thus low collision rates) simply skip step 1) and do
		// not sort the array at all. A zero collision rate implies that the array
		// is sorted (except for first PROBE_LIMIT slots) if fingerprints wrapped around.
		// c) Select just 1..N partitions out of the set of all array partitions
		// for which the closest pair gets calculated. This is a more extreme variant
		// of the current approximation which skips fingerprints on disk.
		
		// 1) Sort all fingerprints, either with a sequential or concurrent
		// flusher depending on the size of the array.
		final int numThreads = TLCGlobals.getNumWorkers();
		this.flusher = getFlusher(numThreads, getTblCnt());
		this.flusher.prepareTable();
		
		// 2) A task finds the pair with the minimum distance in an ordered
		// subrange of array. Each task is assigned an id. This id determines
		// which subrange of array (partition) it searches.
		final Collection<Callable<Long>> tasks = new ArrayList<Callable<Long>>(numThreads);
		final long length = (long) Math.floor(array.size() / (double) numThreads);
		for (int i = 0; i < numThreads; i++) {
			final int id = i;
			tasks.add(new Callable<Long>() {
				@Override
				public Long call() throws Exception {
					final boolean isLast = id == numThreads - 1;
					final long start = id * length;
					// Partitions overlap in case the two fingerprints with
					// minimum distance are in two adjacent partitions.
					final long end = (isLast ? array.size() - 1L : start + length) + 1L;
					
					long distance = Long.MAX_VALUE;
					
					// Reuse Iterator implementation which already handles the
					// various cases related to the cyclic table layout. Pass it
					// getTblCnt to make sure next does not keep going forever
					// if the array is empty. Instead, check the itr's position.
					final Iterator itr = new Iterator(array, getTblCnt(), start, indexer,
							isLast && id != 0 ? Iterator.WRAP.FORBIDDEN : Iterator.WRAP.ALLOWED);
					try {
						// If the partition is empty, next throws a NSEE.
						long x = itr.next();
						long y = 0;
						while ((y = itr.next(end)) != EMPTY) {
							long d = y - x;
							// d < 0 indicates that the array is not sorted.
							// d == 0 indicates two identical elements in the
							// fingerprint set. Iff this is the last partition,
							// itr.next might have returned the first element of the
							// first partition.
							assert d > 0 ^ (d < 0 && itr.getPos() > end && isLast);
							distance = Math.min(distance, d);
							x = y;
						}
						return distance;
					} catch (NoSuchElementException e) {
						return distance;
					}
				}
			});
		}
		
		// Start as many tasks as we have workers. Afterwards, collect the
		// minimum distance out of the set of results provided by the workers.
		final ExecutorService executorService = Executors.newFixedThreadPool(numThreads);
		try {
			final long distance = executorService.invokeAll(tasks).stream().min(new Comparator<Future<Long>>() {
				public int compare(Future<Long> o1, Future<Long> o2) {
					try {
						return Long.compare(o1.get(), o2.get());
					} catch (InterruptedException e) {
						Thread.currentThread().interrupt();
						throw new OffHeapRuntimeException(e);
					} catch (ExecutionException e) {
						throw new OffHeapRuntimeException(e);
					}
				}
			}).get().get();
			return distance;
		} catch (InterruptedException ie) {
			Thread.currentThread().interrupt();
			throw new OffHeapRuntimeException(ie);
		} catch (ExecutionException e) {
			throw new OffHeapRuntimeException(e);
		} finally {
			executorService.shutdown();
		}
		
		
		// Dynamic variant to maintain closest pair:
		// The dynamic (during insertions and not on static data) variant of the closest
		// pair problem also provides an approximation of the actual closest pair. It
		// can be maintained with little overhead in runtime and space and returned in
		// constant time O(1). Contrary to the current implementation, it does not skip
		// fingerprints on disk but observes all fingerprints.
		// For that, we observe the minimum distance OD of the fingerprint to be inserted
		// and all fingerprints it collides with in the method memInsert0. Before
		// returning from memInsert0, the global minimum distance GD gets updated to the
		// observed distance OD iff OD < GD (for scalability reasons we want to use a
		// java.util.concurrent.atomic.LongAccumulator).
		// This provides a sufficient approximation iff the collision rate is
		// sufficiently high. Under a low collision rate, the number of comparisons in
		// memInsert0 will be low. But even under a high collision rate, the
		// approximation GD does not necessarily converge with the real minimum distance:
		// Let f1 differs from f2 in just the lowest significant bit (LSB) and let f1 <
		// f2. Depending on the size of the array, it is possible that f1 and f2 are
		// indexed to two adjacent positions. If both positions for f1 and f2 are empty
		// by the time f1 and f2 get inserted, no distance for f1 and f2 will be
		// calculated.
		// For low hash table/array collision rates (small load factors), we could
		// simply report "insufficient data". Users will still have the optimistic FP64
		// collision probability, which will also be very small.
	}

	//**************************** Indexer ****************************//
	
	public static class Indexer {

		private static final long minFingerprint = 1L; //Minimum possible fingerprint (0L marks an empty position)

		private final double tblScalingFactor;
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
			return (fp & prefixMask) >>> rShift;
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
			@Override
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
				} else if (wrappedA ^ wrappedB) {
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
		int loPage = 0;
		int hiPage = indexLength - 1;
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
		assert this.index[loPage] < fp && fp < this.index[hiPage];
		
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
		
		assert isHigher(midEntry, fp, raf);
		return midEntry;
	}

	public boolean isHigher(long midEntry, long fp, BufferedRandomAccessFile raf) throws IOException {
		raf.seek((midEntry - 1L) * LongSize);
		final long low = raf.readLong();
		final long high = raf.readLong();
		if (low < fp && fp < high) {
			return true;
		}
		return false;
	}

	public class ConcurrentOffHeapMSBFlusher extends OffHeapMSBFlusher {
		
		private final int numThreads;
		private final ExecutorService executorService;
		private final int r; 
		private final long insertions;
		/**
		 * The length of a single partition.
		 */
		private final long length;
		private List<Result> offsets; 

		public ConcurrentOffHeapMSBFlusher(final LongArray array, final int r, final int numThreads,
				final long insertions) {
			super(array);
			this.r = r;
			this.numThreads = numThreads;
			this.insertions = insertions;

			this.length = (long) Math.floor(a.size() / (double) numThreads);
			this.executorService = Executors.newFixedThreadPool(numThreads);
		}
		
		/* (non-Javadoc)
		 * @see tlc2.tool.fp.DiskFPSet.Flusher#prepareTable()
		 */
		@Override
		protected void prepareTable() {
			final long now = System.currentTimeMillis();
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
						LongArrays.sort(a, isFirst ? 0L : start + 1L, end, getLongComparator());
						assert checkSorted(a, indexer, r, isFirst ? 0L : start + 1L, end) == -1L : String.format(
								"Array %s not fully sorted at index %s and reprobe %s in range [%s,%s].", a.toString(),
								checkSorted(array, indexer, r, start, end), r, start, end);
						
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
						final long occupied = getTableOffset(a, r, indexer, start, limit);
						assert occupied <= limit - start;
						
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
				offsets = futuresToResults(executorService.invokeAll(tasks));
			} catch (InterruptedException ie) {
				Thread.currentThread().interrupt();
				throw new OffHeapRuntimeException(ie);
			} catch (ExecutionException notExpectedToHappen) {
				throw new OffHeapRuntimeException(notExpectedToHappen);
			}

			assert checkSorted(a, indexer, r) == -1L : String.format(
					"Array %s not fully sorted at index %s and reprobe %s.", a.toString(),
					checkSorted(array, indexer, r), r);
			
			LOGGER.log(Level.FINE, "Sorted in-memory table with {0} workers and reprobe {1} in {2} ms.",
					new Object[] { numThreads, r, System.currentTimeMillis() - now });
		}
		
		private List<Result> futuresToResults(List<Future<Result>> futures) throws InterruptedException, ExecutionException {
			final List<Result> res = new ArrayList<Result>(futures.size());
			for (Future<Result> future : futures) {
				res.add(future.get());
			}
			return res;
		}

		@Override
		protected void mergeNewEntries(final BufferedRandomAccessFile[] inRAFs, final RandomAccessFile outRAF, final Iterator ignored) throws IOException {
			final long now = System.currentTimeMillis();
			assert offsets.stream().mapToLong(new ToLongFunction<Result>() {
				public long applyAsLong(Result result) {
					return result.getTable();
				}
			}).sum() == insertions : "Missing inserted elements during eviction.";
			assert offsets.stream().mapToLong(new ToLongFunction<Result>() {
				public long applyAsLong(Result result) {
					return result.getDisk();
				}
			}).sum() == fileCnt : "Missing disk elements during eviction.";

			// Calculate offsets for in and the out file, i.e. sum up the
			// combined number of elements in lower partitions.
			for (int id = 1; id < numThreads; id++) {
				final Result prev = offsets.get(id - 1);
				final Result result = offsets.get(id);
				result.setInOffset(prev.getInOffset() + prev.getDisk());
				result.setOutOffSet(prev.getOutOffset() + prev.getTotal());
			}

			final long outLength = outRAF.length();
			final Collection<Callable<Void>> tasks = new ArrayList<Callable<Void>>(numThreads);
			final BufferedRandomAccessFile[] tmpRAFs = new BufferedRandomAccessFile[numThreads];
			for (int i = 0; i < numThreads; i++) {
				final int id = i;
				
				// Create a new RAF instance. The outRAF instance is
				// otherwise shared by multiple writers leading to race
				// conditions and inconsistent fingerprint set files.
				tmpRAFs[id] = new BufferedRandomAccessFile(new File(tmpFilename), "rw");
				tmpRAFs[id].setLength(outLength);

				// Set offsets into the out (tmp) file.
				final Result result = offsets.get(id);
				tmpRAFs[id].seekAndMark(result.getOutOffset() * FPSet.LongSize);

				// Set offset and the number of elements the
				// iterator is supposed to return.
				final Iterator itr = new Iterator(a, result.getTable(), id * length, indexer,
						id == 0 ? Iterator.WRAP.ALLOWED : Iterator.WRAP.FORBIDDEN);
				
				final BufferedRandomAccessFile inRAF = inRAFs[id];
				assert (result.getInOffset() + result.getDisk()) * FPSet.LongSize <= inRAF.length();
				inRAF.seekAndMark(result.getInOffset() * FPSet.LongSize);

				// Stop reading after diskReads elements (after
				// which the next thread continues) except for the
				// last thread which reads until EOF. Pass 0 when
				// nothing can be read from disk.
				final long diskReads = id == numThreads - 1 ? fileCnt - result.getInOffset() : result.getDisk();
				
				tasks.add(new Callable<Void>() {
					public Void call() throws Exception {
						ConcurrentOffHeapMSBFlusher.super.mergeNewEntries(inRAF, tmpRAFs[id], itr, diskReads);
						assert tmpRAFs[id].getFilePointer() == (result.getOutOffset() + result.getTotal()) * FPSet.LongSize : id
								+ " writer did not write expected amount of fingerprints to disk.";
						return null;
					}
				});
			}
			// Combine the callable results.
			try {
				executorService.invokeAll(tasks);
				executorService.shutdown();
				executorService.awaitTermination(Long.MAX_VALUE, TimeUnit.MILLISECONDS);
				assert checkRAFs(tmpRAFs);
			} catch (InterruptedException ie) {
				Thread.currentThread().interrupt();
				throw new OffHeapRuntimeException(ie);
			} finally {
				executorService.shutdown();
			}
			
			// Finally close the out rafs after all tasks have finished. On
			// Linux, closing an instance of the tmpRAFs appears to be racy when
			// other tasks still execute.
			for (int i = 0; i < tmpRAFs.length; i++) {
				tmpRAFs[i].close();
			}

			assert checkRAFs(inRAFs);
			assert checkTable(a) : "Missed element during eviction.";
			
			LOGGER.log(Level.FINE, "Wrote table to disk with {0} workers in {1} ms.",
					new Object[] { numThreads, (System.currentTimeMillis() - now) });
		}

		private class Result {
			private final long occupiedTable;
			private final long occupiedDisk;
			private long outOffset;
			private long inOffset;
			
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
			public void setOutOffSet(long offset) {
				this.outOffset = offset;
			}
			public void setInOffset(long offset) {
				this.inOffset = offset;
			}
			public long getInOffset() {
				return this.inOffset;
			}
			public long getOutOffset() {
				return this.outOffset;
			}
		}
	}
	
	public class OffHeapMSBFlusher extends Flusher {
		
		protected final LongArray a;

		public OffHeapMSBFlusher(LongArray array) {
			a = array;
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.DiskFPSet.Flusher#prepareTable()
		 */
		@Override
		protected void prepareTable() {
			super.prepareTable();
			final int r = PROBE_LIMIT;
			
			assert checkInput(array, indexer, r) : "Table violates invariants prior to eviction";
			
			// Sort with a single thread.
			LongArrays.sort(a, 0, a.size() - 1L + r, getLongComparator());

			assert checkSorted(a, indexer, r) == -1L : String.format(
					"Array %s not fully sorted at index %s and reprobe %s.", a.toString(),
					checkSorted(array, indexer, r), r);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.MSBDiskFPSet#mergeNewEntries(java.io.RandomAccessFile, java.io.RandomAccessFile)
		 */
		@Override
		protected void mergeNewEntries(BufferedRandomAccessFile[] inRAFs, RandomAccessFile outRAF) throws IOException {
			final long buffLen = tblCnt.sum();
			final Iterator itr = new Iterator(array, buffLen, indexer);

			final int indexLen = calculateIndexLen(buffLen);
			index = new long[indexLen];
			mergeNewEntries(inRAFs, outRAF, itr);

			final long length = (outRAF.length() / LongSize) - 1L;
			writeIndex(index, outRAF, length);
			assert checkIndex(index) : "Broken disk index.";
			assert checkIndex(index, outRAF, length) : "Misaligned disk index.";
			
			// maintain object invariants
			fileCnt += buffLen;
		}

		protected void mergeNewEntries(BufferedRandomAccessFile[] inRAFs, RandomAccessFile outRAF, Iterator itr)
				throws IOException {
			inRAFs[0].seek(0);
			mergeNewEntries(inRAFs[0], outRAF, itr, inRAFs[0].length() / FPSet.LongSize);
		}

		/*
		 * See PlusCal spec OpenAddressing.ConcurrentFlusher.tla which has been checked for Nat == 0..6.
		 */
		protected void mergeNewEntries(BufferedRandomAccessFile inRAF, RandomAccessFile outRAF, final Iterator itr,
				long diskReads) throws IOException {
			
			// Disk might be empty.
			long value = 0L;
			if (diskReads > 0) {
				value = inRAF.readLong();
			} else {
				assert fileCnt == 0L;
			}
			
			long tableReads = itr.elements;
			long fp = itr.markNext();
			
			do {
				if (value == fp) {
					MP.printWarning(EC.TLC_FP_VALUE_ALREADY_ON_DISK, String.valueOf(value));
				}
				assert fp > EMPTY : "Wrote an invalid fingerprint to disk.";
				
				// From memory/table
		        if (tableReads > 0 && (fp < value || diskReads == 0)) {
					outRAF.writeLong(fp);
					tableReads--;
					diskWriteCnt.increment();
					// Read next value if any.
		            if (tableReads > 0) {
						final long nextFP = itr.markNext();
						assert nextFP > fp : nextFP + " > " + fp + " from table at pos " + itr.pos + " "
								+ a.toString(itr.pos - 10L, itr.pos + 10L);
						fp = nextFP;
		            }
		         }
		         
		         // From file/disk
				if (diskReads > 0 && (value < fp || tableReads == 0)) {
					outRAF.writeLong(value);
					diskReads--;
					diskWriteCnt.increment();
					// Read next value if any.
					if (diskReads > 0) {
						final long nextValue = inRAF.readLong();
						assert value < nextValue;
						value = nextValue;
					}
				}

			} while (diskReads > 0 || tableReads > 0);
			
			// both sets used up completely
			Assert.check(diskReads == 0L && tableReads == 0L, EC.GENERAL);
			assert !itr.hasNext();
		}
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#calculateIndexLen(long)
	 */
	@Override
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

	protected void writeIndex(long[] index, final RandomAccessFile raf, long length) throws IOException {
		for (int i = 0; i < index.length; i++) {
			long pos = Math.min(((long) i) * NumEntriesPerPage, length);
			raf.seek(pos * LongSize);
			final long value = raf.readLong();
			index[i] = value;
		}
	}
	
	/**
	 * A non-thread safe Iterator whose next method returns the next largest
	 * element.
	 */
	public static class Iterator {

		private enum WRAP {
			ALLOWED, FORBIDDEN;
		}

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

		public long getPos() {
			return pos;
		}

		/**
		 * Returns the next element in the iteration that is not EMPTY nor
		 * marked evicted.
		 *
		 * @return the next element in the iteration that is not EMPTY nor
		 *         marked evicted.
		 * @exception NoSuchElementException
		 *                iteration has no more elements.
		 */
		public long next() {
			return next0(false, Long.MAX_VALUE);
		}
		
		long next(long maxPos) {
			if (pos >= maxPos) {
				return EMPTY;
			}
			return next0(false, maxPos);
		}
		
		/**
		 * Returns the next element in the iteration that is not EMPTY nor
		 * marked evicted and marks it to be evicted.
		 * <p>
		 * THIS IS NOT SIDEEFFECT FREE. AFTERWARDS, THE ELEMENT WILL BE MARKED
		 * EVICTED.
		 *
		 * @return the next element in the iteration that is not EMPTY nor
		 *         marked evicted.
		 * @exception NoSuchElementException
		 *                iteration has no more elements.
		 */
		public long markNext() {
			return next0(true, Long.MAX_VALUE);
		}

		private long next0(final boolean mark, final long maxPos) {
			long elem;
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
				if (mark) {array.set(position, elem | MARK_FLUSHED);}
				elementsRead = elementsRead + 1L;
				return elem;
			} while (hasNext() && pos < maxPos);
			if (pos >= maxPos) {
				return EMPTY;
			}
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

	public static class OffHeapRuntimeException extends RuntimeException {

		public OffHeapRuntimeException(Exception ie) {
			super(ie);
		}
	}
	
	// ***************** assertion helpers *******************//

	private static boolean checkInput(final LongArray array, final Indexer indexer, final int reprobe) {
		for (long pos = 0; pos <= array.size() + reprobe - 1L; pos++) {
			long tmp = array.get(pos % array.size());
			if (tmp == EMPTY) {
				continue;
			}
			if (tmp < EMPTY) {
				// Convert evicted fps back.
				tmp = tmp & FLUSHED_MASK;
			}
			final long idx = indexer.getIdx(tmp);
			// Accept wrapped elements.
			if (pos < reprobe && idx > (array.size() - 1L - pos - reprobe)) {
				continue;
			}
			// Accept non-wrapped elements when pos > array.size
			if (pos > array.size() - 1L && idx + reprobe < pos) {
				continue;
			}
			// Accept any other valid elements where pos is within the range
			// given by [idx,idx + reprobe].
			if (idx <= pos && pos <= idx + reprobe) {
				continue;
			}
			System.err.println(String.format("%s with idx %s at pos %s (reprobe: %s).", tmp, idx, pos, reprobe));
			return false;
		}
		return true;
	}

	/**
	 * @return -1L iff array is sorted, index/position of the element that violates otherwise in the range [start, end].
	 */
	private static long checkSorted(final LongArray array, final Indexer indexer, int reprobe, long start, long end) {
		if (reprobe >= array.size()) {
			// When the array is smaller than the number of positions/slots, the
			// loop below will run past its bounds. If this happens, it compares
			// elements the element at the start with the element at the end.
			reprobe = (int) (array.size() - 1);
		}
		long e = 0L;
		for (long pos = start; pos <= end; pos++) {
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
				System.err.println(String.format("%s >= %s at pos %s.", e, tmp, pos));
				return pos;
			}
			e = tmp;
		}
		return -1L;
	}

	/**
	 * @return -1L iff array is sorted, index/position of the element that violates otherwise.
	 */
	private static long checkSorted(final LongArray array, final Indexer indexer, final int reprobe) {
		return checkSorted(array, indexer, reprobe, 0, array.size() - 1L + reprobe);
	}

	private static boolean checkRAFs(final BufferedRandomAccessFile[] rafs) throws IOException {
		for (int i = 0; i < rafs.length - 1; i++) {
			final long end = rafs[i].getFilePointer();
			final long start = rafs[i + 1].getMark();
			if (end != start) {
				return false;
			}
		}
		return true;
	}
	
	private static boolean checkTable(LongArray array) {
		for (long i = 0L; i < array.size(); i++) {
			long elem = array.get(i);
			if (elem > EMPTY) {
				System.err.println(String.format("%s elem at pos %s.", elem, i));
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
	
	private static boolean checkIndex(final long[] idx, final RandomAccessFile raf, final long length) throws IOException {
		for (long i = 0L; i < idx.length; i++) {
			final long pos = Math.min(i * NumEntriesPerPage, length);
			raf.seek(pos * LongSize);
			final long value = raf.readLong();
			final long index = idx[(int) i];
			if (value != index) {
				return false;
			}
		}
		return true;
	}
}
