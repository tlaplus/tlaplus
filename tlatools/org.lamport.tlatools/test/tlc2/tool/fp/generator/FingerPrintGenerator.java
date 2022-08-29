// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp.generator;

import org.junit.Assert;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MultiThreadedFPSetTest;

import java.io.IOException;
import java.util.Random;
import java.util.concurrent.BrokenBarrierException;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.CyclicBarrier;

public class FingerPrintGenerator implements Runnable {

    protected final long totalInsertions;
    protected final long perThreadInsertions;
    protected final long seed;
    protected final Random rnd;
    protected final FPSet fpSet;
    protected final CountDownLatch latch;
    protected final CyclicBarrier barrier;
    protected final int id;
    protected final int numThreads;
    protected final MultiThreadedFPSetTest test;
    protected long puts = 0L;
    protected long collisions = 0L;

    public FingerPrintGenerator(final MultiThreadedFPSetTest test, final int id, final int numThreads, final FPSet fpSet, final CountDownLatch latch,
                                final long seed, final long totalInsertions, final CyclicBarrier barrier) {
        this.test = test;
        this.id = id;
        this.numThreads = numThreads;
        this.fpSet = fpSet;
        this.latch = latch;
        this.barrier = barrier;
        this.seed = seed;
        this.rnd = new Random(seed);
        this.totalInsertions = totalInsertions;
        this.perThreadInsertions = (long) Math.floor(totalInsertions / numThreads);
    }

    /* (non-Javadoc)
     * @see java.lang.Runnable#run()
     */
    @Override
    public void run() {
        waitForAllThreadsStarted();

        long predecessor = 0L;
        // Reduce number of FPSet#size invocation by counting puts/collisions.
        // FPSet#size can cause an FPSet to synchronize all its writers slowing
        // down execution.
        while (puts + collisions < perThreadInsertions || fpSet.size() < totalInsertions) {
            try {
                // make sure set still contains predecessor
                if (predecessor != 0L) {
                    Assert.assertTrue(fpSet.contains(predecessor));
                }

                predecessor = rnd.nextLong();

                // Periodically verify the FPSet's content. This causes a
                // drastic slow down.
//				if (fpSet.size() % 10000 == 0) {
//					final Random verify = new Random(seed);
//					long fp = verify.nextLong();
//					while (fp != predecessor) {
//						Assert.assertTrue(fpSet.contains(fp));
//						fp = verify.nextLong();
//					}
//				}
//				
                final boolean put = fpSet.put(predecessor);
                if (!put) {
                    puts++;
                } else {
                    collisions++;
                }
            } catch (final IOException e) {
                e.printStackTrace();
                Assert.fail("Unexpected");
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
        return collisions;
    }

    protected void waitForAllThreadsStarted() {
        try {
            barrier.await();
        } catch (final InterruptedException | BrokenBarrierException e1) {
            e1.printStackTrace();
        }
    }
}