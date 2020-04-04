// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.Date;
import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.CyclicBarrier;

import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;

import tlc2.TLCGlobals;
import tlc2.tool.fp.generator.BatchedFingerPrintGenerator;
import tlc2.tool.fp.generator.FingerPrintGenerator;
import tlc2.tool.fp.generator.LongVecFingerPrintGenerator;
import tlc2.tool.fp.generator.PartitionedFingerPrintGenerator;
import tlc2.util.IdThread;

public abstract class MultiThreadedFPSetTest extends AbstractFPSetTest {

	private static final int NUM_THREADS = Integer.getInteger(MultiThreadedFPSetTest.class.getName() + ".numThreads",
			Runtime.getRuntime().availableProcessors());
	private static final long INSERTIONS = Long.getLong(MultiThreadedFPSetTest.class.getName() + ".insertions",
			Integer.MAX_VALUE + 2L);

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	@Before
	public void printStats() throws Exception {
		System.out.println("Insertions: " + df.format(INSERTIONS)
				+ " (approx: " + df.format(INSERTIONS * FPSet.LongSize >> 20) + " GiB)");
		System.out.println("Thread count: " + NUM_THREADS);
	}
	
	/**
	 * Test filling a {@link FPSet} with random fingerprints using multiple
	 * threads in ordered batches
	 */
	@Test
	public void testMaxFPSetSizeRndBatched() throws IOException, InterruptedException, NoSuchMethodException, SecurityException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		doTest(BatchedFingerPrintGenerator.class);
	}
	
	/**
	 * Test filling a {@link FPSet} with random fingerprints using multiple
	 * threads in ordered LongVecs using putBlock/containsBlock
	 */
	@Test
	public void testMaxFPSetSizeRndBlock() throws IOException, InterruptedException, NoSuchMethodException, SecurityException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		doTest(LongVecFingerPrintGenerator.class);
	}
	
	/**
	 * Test filling a {@link FPSet} with max int + 2L random using multiple
	 * threads
	 */
	@Test
	public void testMaxFPSetSizeRnd() throws IOException, InterruptedException, NoSuchMethodException, SecurityException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		doTest(FingerPrintGenerator.class);
	}
	
	/**
	 * Test filling a {@link FPSet} with multiple threads. Each thread accesses
	 * a disjunct partition of the key space and fills it up linearly. This
	 * prevents hash collisions as well as lock contention. Essentially, this is
	 * the best case scenario. It ignores INSERTIONS for now.
	 */
	@Test
	public void testMaxFPSetSizePartitioned() throws IOException, InterruptedException, NoSuchMethodException, SecurityException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		doTest(PartitionedFingerPrintGenerator.class);
	}
	
	/**
	 * @param fpgClass
	 * @throws IOException
	 * @throws InterruptedException
	 * @throws NoSuchMethodException
	 * @throws SecurityException
	 * @throws InstantiationException
	 * @throws IllegalAccessException
	 * @throws IllegalArgumentException
	 * @throws InvocationTargetException
	 */
	protected FPSet doTest(Class<? extends FingerPrintGenerator> fpgClass) throws IOException, InterruptedException, NoSuchMethodException, SecurityException, InstantiationException, IllegalAccessException, IllegalArgumentException, InvocationTargetException {
		// Skip the test if the property
		// -Dtlc2.tool.fp.MultiThreadedFPSetTest.excludes contains the simple
		// name of the test. I.e.
		// ...excludes=_BatchedFingerPrintGenerator_LongVecFingerPrintGenerator_PartitionedFingerPrintGenerator
		// to skip all but FingerPrintGenerator test. Note that the name has to
		// be prefixed with "_" to make it possible to skip
		// "FingerPrintGenerator" itself.
		Assume.assumeFalse(System.getProperty(MultiThreadedFPSetTest.class.getName() + ".excludes", "")
				.contains("_" + fpgClass.getSimpleName()));
		System.out.println("Running test: " + fpgClass.getSimpleName());
		
		TLCGlobals.setNumWorkers(NUM_THREADS);
		final FPSet fpSet = getFPSetInitialized(NUM_THREADS);
		fpSet.incWorkers(NUM_THREADS);
		final CountDownLatch latch = new CountDownLatch(NUM_THREADS);

		final Constructor<?> constructor = fpgClass.getConstructor(new Class[] { MultiThreadedFPSetTest.class,
				int.class, int.class, FPSet.class, CountDownLatch.class, long.class, long.class, CyclicBarrier.class });
		
		// Take timestamp after instantiating FPSet to not measure zero'ing/initializing FPSet.  
		startTimestamp = System.currentTimeMillis();

		final Timer timer = new Timer();
		final CyclicBarrier barrier = new CyclicBarrier(NUM_THREADS, new Runnable() {
			public void run() {
				// Start a periodic task to report progress. Do not do it as part of the
				// FPGs below. It can drastically slow down an FPG selected to be the
				// reporter.
				final TimerTask reporter = new TimerTask() {
					public void run() {
						final long currentSize = fpSet.size();
						final long insertions = currentSize - previousSize;
						if (fpSet instanceof FPSetStatistic) {
							FPSetStatistic fpSetStatistics = (FPSetStatistic) fpSet;
							System.out.println(System.currentTimeMillis() + " s (epoch); " + df.format(insertions) + " insertions/min; " + pf.format(fpSetStatistics.getLoadFactor()) + " load factor");
						} else {
							System.out.println(System.currentTimeMillis() + " s (epoch); " + df.format(insertions) + " insertions/min");
						}
						previousSize = currentSize;
					}
				};
				// Take timestamp after instantiating FPSet to not measure zero'ing/initializing FPSet.  
				startTimestamp = System.currentTimeMillis();
				timer.scheduleAtFixedRate(reporter, 1L, 60 * 1000);
			}
		});
		
		long seed = RNG_SEED;
		final FingerPrintGenerator[] fpgs = new FingerPrintGenerator[NUM_THREADS];
		for (int i = 0; i < fpgs.length; i++) {
			fpgs[i] = (FingerPrintGenerator) constructor.newInstance(
					this, i, fpgs.length, fpSet, latch, seed++, INSERTIONS, barrier);
			Thread thread = new IdThread(fpgs[i], "Producer#" + i, i);
			thread.start();
		}

		// wait for runnables/fpg to tear down the latch
		latch.await();
		endTimeStamp = new Date();
		
		// Cancel reporting task.
		timer.cancel();
		
		long overallPuts = 0L;
		long overallCollisions = 0L;
		
		// print stats
		for (int i = 0; i < fpgs.length; i++) {
			final FingerPrintGenerator fpg = fpgs[i];
			long puts = fpg.getPuts();
			long collisions = fpg.getCollisions();
			System.out.println(String.format("Producer: %s, puts: %s, puts/collisions: %s", fpg.getId(), puts,
					(collisions == 0 ? "none" : (double) (puts / collisions))));
			overallPuts += puts;
			overallCollisions += collisions;
		}
		System.out.println(String.format("Total puts: %s, total collisions: %s, total load factor: %s, duration: %s ms.", overallPuts,
				overallCollisions, df.format(((FPSetStatistic) fpSet).getLoadFactor()), endTimeStamp.getTime() - startTimestamp));
		printInsertionSpeed(fpSet, startTimestamp, endTimeStamp.getTime());
		
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
		
		return fpSet;
	}
}
