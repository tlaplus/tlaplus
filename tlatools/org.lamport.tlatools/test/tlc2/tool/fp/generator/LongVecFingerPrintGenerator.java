// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp.generator;

import org.junit.Assert;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MultiThreadedFPSetTest;
import tlc2.util.LongVec;

import java.io.IOException;
import java.util.Arrays;
import java.util.BitSet;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.CyclicBarrier;

public class LongVecFingerPrintGenerator extends FingerPrintGenerator {

    private static final int batch = 1024;

    public LongVecFingerPrintGenerator(final MultiThreadedFPSetTest test, final int id, final int numThreads, final FPSet fpSet, final CountDownLatch latch, final long seed, final long insertions, final CyclicBarrier barrier) {
        super(test, id, numThreads, fpSet, latch, seed, insertions, barrier);
    }

    /* (non-Javadoc)
     * @see java.lang.Runnable#run()
     */
    @Override
    public void run() {
        waitForAllThreadsStarted();

        final TestLongVec predecessors = new TestLongVec(batch);
        boolean initialized = false;
        // Reduce number of FPSet#size invocation by counting puts/collisions.
        // FPSet#size can cause an FPSet to synchronize all its writers slowing
        // down execution.
        while (puts + collisions < perThreadInsertions || fpSet.size() < totalInsertions) {
            try {
                // Make sure set still contains predecessors
                if (initialized) {
                    final BitSet bitVector = fpSet.containsBlock(predecessors);
                    Assert.assertEquals(batch, batch - bitVector.cardinality());
                }

                // Fill new fingerprints and sort them
                for (int i = 0; i < batch; i++) {
                    predecessors.setElement(i, rnd.nextLong());
                }
                initialized = true;
                predecessors.sort();

                // Add sorted batch to fpset
                final BitSet bitVector = fpSet.putBlock(predecessors);
                puts += bitVector.cardinality();
                collisions += (batch - bitVector.cardinality());
            } catch (final IOException e) {
                e.printStackTrace();
                Assert.fail("Unexpected");
            }
        }
        latch.countDown();
    }

    // This implementation adds two methods that should be used with caution as
    // they mess with the internal capacity checks of LongVec. We don't want to
    // make them API.
    private static class TestLongVec extends LongVec {

        private static final long serialVersionUID = -720614225756936980L;

        public TestLongVec(final int batch) {
            super(batch);
        }

        public final void sort() {
            Arrays.sort(elementData);
        }

        public final void setElement(final int index, final long x) {
            this.elementData[index] = x;
            this.elementCount = ++elementCount % elementData.length + 1;
        }
    }
}