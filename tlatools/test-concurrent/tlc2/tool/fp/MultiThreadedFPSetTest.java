// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.IOException;
import java.util.Arrays;
import java.util.Date;
import java.util.Random;
import java.util.concurrent.CountDownLatch;

public abstract class MultiThreadedFPSetTest extends AbstractFPSetTest {

	private static final int NUM_THREADS = Integer.getInteger(MultiThreadedFPSetTest.class.getName() + ".numThreads",
			2);
	private static final long INSERTIONS = Long.getLong(MultiThreadedFPSetTest.class.getName() + ".insertions",
			Integer.MAX_VALUE + 2L);

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();
		System.out.println("Insertions: " + df.format(INSERTIONS)
				+ " (approx: " + df.format(INSERTIONS * FPSet.LongSize >> 20) + " GiB)");
		System.out.println("Thread count: " + NUM_THREADS);
	}
	
	
	/**
	 * Test filling a {@link FPSet} with random fingerprints using multiple
	 * threads in ordered batches
	 * 
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public void testMaxFPSetSizeRndBatched() throws IOException, InterruptedException {
		final FPSet fpSet = getFPSetInitialized(NUM_THREADS);
		final CountDownLatch latch = new CountDownLatch(NUM_THREADS);

		long seed = 15041980L;
		final FingerPrintGenerator[] fpgs = new FingerPrintGenerator[NUM_THREADS];
		for (int i = 0; i < fpgs.length; i++) {
			fpgs[i] = new BatchedFingerPrintGenerator(i, fpSet, latch, seed++, INSERTIONS);
			Thread thread = new Thread(fpgs[i], "Producer#" + i);
			thread.start();
		}

		// wait for runnables/fpg to tear down the latch
		latch.await();

		endTimeStamp = new Date();
		
		long overallPuts = 0L;
		
		// print stats
		for (int i = 0; i < fpgs.length; i++) {
			final FingerPrintGenerator fpg = fpgs[i];
			long puts = fpg.getPuts();
			System.out.println("Producer: " + fpg.getId() + " puts: " + puts);
			System.out.println("puts/collisions: " + (double) (puts / fpg.getCollisions()));
			overallPuts += puts;
		}
		
		// Do not compare fpSet.size() to insertions as several FPGs might race
		// with the FPG that inserts the INSERTIONS element. Hence we count the
		// overallPuts externally and compare it to the size of the fpSet.
		// Additionally we assert that the fpSet has at least the seen
		// INSERTIONS elements and that maximally NUM_THREADS extra elements are
		// in the fpSet.
		assertEquals(overallPuts, fpSet.size());
		assertTrue(fpSet.size() >= INSERTIONS);
		assertTrue(fpSet.size() <= INSERTIONS + NUM_THREADS);
		
		// Check a DiskFPSet's invariant that after flush all fingerprints in
		// the file are a) monotonically increasing and b) there are no duplicates.
		assertTrue(fpSet.checkInvariant());
	}
	
	/**
	 * Test filling a {@link FPSet} with max int + 2L random using multiple
	 * threads
	 * 
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public void testMaxFPSetSizeRnd() throws IOException, InterruptedException {
		final FPSet fpSet = getFPSetInitialized(NUM_THREADS);
		final CountDownLatch latch = new CountDownLatch(NUM_THREADS);

		long seed = 15041980L;
		final FingerPrintGenerator[] fpgs = new FingerPrintGenerator[NUM_THREADS];
		for (int i = 0; i < fpgs.length; i++) {
			fpgs[i] = new FingerPrintGenerator(i, fpSet, latch, seed++, INSERTIONS);
			Thread thread = new Thread(fpgs[i], "Producer#" + i);
			thread.start();
		}

		// wait for runnables/fpg to tear down the latch
		latch.await();

		endTimeStamp = new Date();
		
		long overallPuts = 0L;
		
		// print stats
		for (int i = 0; i < fpgs.length; i++) {
			final FingerPrintGenerator fpg = fpgs[i];
			long puts = fpg.getPuts();
			System.out.println("Producer: " + fpg.getId() + " puts: " + puts);
			System.out.println("puts/collisions: " + (double) (puts / fpg.getCollisions()));
			overallPuts += puts;
		}
		
		// Do not compare fpSet.size() to insertions as several FPGs might race
		// with the FPG that inserts the INSERTIONS element. Hence we count the
		// overallPuts externally and compare it to the size of the fpSet.
		// Additionally we assert that the fpSet has at least the seen
		// INSERTIONS elements and that maximally NUM_THREADS extra elements are
		// in the fpSet.
		assertEquals(overallPuts, fpSet.size());
		assertTrue(fpSet.size() >= INSERTIONS);
		assertTrue(fpSet.size() <= INSERTIONS + NUM_THREADS);
		
		// Check a DiskFPSet's invariant that after flush all fingerprints in
		// the file are a) monotonically increasing and b) there are no duplicates.
		assertTrue(fpSet.checkInvariant());
	}

	public class FingerPrintGenerator implements Runnable {

		protected final long insertions;
		protected final Random rnd;
		protected final FPSet fpSet;
		protected final CountDownLatch latch;
		protected final int id;
		protected long puts = 0L;
		protected long collisions = 0L;

		public FingerPrintGenerator(int id, FPSet fpSet, CountDownLatch latch, long seed, long insertions) {
			this.id = id;
			this.fpSet = fpSet;
			this.latch = latch;
			this.rnd = new Random(seed);
			this.insertions = insertions;
		}

		/* (non-Javadoc)
		 * @see java.lang.Runnable#run()
		 */
		public void run() {
			long predecessor = 0L;
			while (fpSet.size() < insertions) {
				try {
					// make sure set still contains predecessor
					if (predecessor != 0L) {
						assertTrue(fpSet.contains(predecessor));
					}

					predecessor = rnd.nextLong();

					boolean put = fpSet.put(predecessor);
					if (put == false) {
						puts++;
					} else {
						collisions++;
					}

					// First producer prints stats
					if (id == 0) {
						printInsertionSpeed(fpSet.size());
					}

				} catch (IOException e) {
					e.printStackTrace();
					fail("Unexpected");
				}
			}
			latch.countDown();
		}

		public int getId() {
			return id;
		}

		/**
		 * @return the puts
		 */
		public long getPuts() {
			return puts;
		}

		/**
		 * @return the collisions
		 */
		public long getCollisions() {
			return collisions == 0 ? 1 : collisions;
		}
	}
	
	public class BatchedFingerPrintGenerator extends FingerPrintGenerator {

		private static final int batch = 1024;
		
		public BatchedFingerPrintGenerator(int id, FPSet fpSet, CountDownLatch latch, long seed, long insertions) {
			super(id, fpSet, latch, seed, insertions);
		}
		
		/* (non-Javadoc)
		 * @see java.lang.Runnable#run()
		 */
		public void run() {
			long predecessors[] = new long[batch];
			boolean initialized = false;
			while (fpSet.size() < insertions) {
				try {
					// Make sure set still contains predecessors
					if (initialized) {
						for (int i = 0; i < predecessors.length; i++) {
							long predecessor = predecessors[i];
							assertTrue(fpSet.contains(predecessor));
						}
					}

					// Fill new fingerprints and sort them
					for (int i = 0; i < predecessors.length; i++) {
						predecessors[i] = rnd.nextLong();
					}
					initialized = true;
					Arrays.sort(predecessors);

					// Add sorted batch to fpset
					for (int i = 0; i < predecessors.length; i++) {
						long predecessor = predecessors[i];
						boolean put = fpSet.put(predecessor);
						if (put == false) {
							puts++;
						} else {
							collisions++;
						}
					}

					// First producer prints stats
					if (id == 0) {
						printInsertionSpeed(fpSet.size());
					}

				} catch (IOException e) {
					e.printStackTrace();
					fail("Unexpected");
				}
			}
			latch.countDown();
		}
	}
}
