// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.IOException;
import java.util.Random;
import java.util.concurrent.CountDownLatch;

public abstract class MultiThreadedFPSetTeset extends AbstractFPSetTest {

	private static final int NUM_THREADS = Integer.getInteger(MultiThreadedFPSetTeset.class.getName() + ".numThreads",
			2);
	private static final long INSERTIONS = Long.getLong(MultiThreadedFPSetTeset.class.getName() + ".insertions",
			Integer.MAX_VALUE + 2L);

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();
		System.out.println("Thread count: " + NUM_THREADS);
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

		long overAllPuts = 0L;
		
		// print stats
		for (int i = 0; i < fpgs.length; i++) {
			final FingerPrintGenerator fpg = fpgs[i];
			long puts = fpg.getPuts();
			System.out.println("Producer: " + fpg.getId() + " puts: " + puts);
			System.out.println("puts/collisions: " + (double) (puts / fpg.getCollisions()));
			overAllPuts += puts;
		}
		
		assertEquals(overAllPuts, fpSet.size());
		assertEquals(INSERTIONS - 1, fpSet.size());
	}

	public class FingerPrintGenerator implements Runnable {

		private final long insertions;
		private final Random rnd;
		private final FPSet fpSet;
		private final CountDownLatch latch;
		private final int id;
		private long puts = 0L;
		private long collisions = 0L;

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
}
