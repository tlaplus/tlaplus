// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp.generator;

import org.junit.Assert;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MultiThreadedFPSetTest;

import java.io.IOException;
import java.util.Arrays;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.CyclicBarrier;

public class BatchedFingerPrintGenerator extends FingerPrintGenerator {

    private static final int batch = 1024;

    public BatchedFingerPrintGenerator(final MultiThreadedFPSetTest test, final int id, final int numThreads, final FPSet fpSet, final CountDownLatch latch, final long seed, final long insertions, final CyclicBarrier barrier) {
        super(test, id, numThreads, fpSet, latch, seed, insertions, barrier);
    }

    /* (non-Javadoc)
     * @see java.lang.Runnable#run()
     */
    @Override
    public void run() {
        waitForAllThreadsStarted();

        final long[] predecessors = new long[batch];
        boolean initialized = false;
        // Reduce number of FPSet#size invocation by counting puts/collisions.
        // FPSet#size can cause an FPSet to synchronize all its writers slowing
        // down execution.
        while (puts + collisions < perThreadInsertions || fpSet.size() < totalInsertions) {
            try {
                // Make sure set still contains predecessors
                if (initialized) {
                    for (final long predecessor : predecessors) {
                        Assert.assertTrue(fpSet.contains(predecessor));
                    }
                }

                // Fill new fingerprints and sort them
                for (int i = 0; i < predecessors.length; i++) {
                    predecessors[i] = rnd.nextLong();
                }
                initialized = true;
                Arrays.sort(predecessors);

                // Add sorted batch to fpset
                for (final long predecessor : predecessors) {
                    final boolean put = fpSet.put(predecessor);
                    if (!put) {
                        puts++;
                    } else {
                        collisions++;
                    }
                }
            } catch (final IOException e) {
                e.printStackTrace();
                Assert.fail("Unexpected");
            }
        }
        latch.countDown();
    }
}