/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package tlc2.tool.fp.generator;

import org.junit.Assert;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MultiThreadedFPSetTest;

import java.io.IOException;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.CyclicBarrier;

public class PartitionedFingerPrintGenerator extends FingerPrintGenerator {

    private final long numOfPerThreadBuckets;
    private final long increment;
    private long fp;

    public PartitionedFingerPrintGenerator(final MultiThreadedFPSetTest test, final int id, final int numThreads, final FPSet fpSet, final CountDownLatch latch,
                                           final long seed, final long insertions, final CyclicBarrier barrier) {
        super(test, id, numThreads, fpSet, latch, seed, insertions, barrier);

        final long numOfTotalBuckets = fpSet.getConfiguration().getMemoryInFingerprintCnt();
        numOfPerThreadBuckets = numOfTotalBuckets / ((long) numThreads);

        final long perThreadStartBucket = numOfPerThreadBuckets * ((long) id);
        increment = (long) Math.ceil((Long.MAX_VALUE - 1L) / (numOfTotalBuckets * 1d));
        fp = increment * perThreadStartBucket;
    }

    /* (non-Javadoc)
     * @see java.lang.Runnable#run()
     */
    @Override
    public void run() {
        waitForAllThreadsStarted();

        long insertions = 0L;

        while (insertions++ < numOfPerThreadBuckets) {
            try {
                if (fp != 0L) {
                    if (fpSet.put(fp)) {
                        Assert.fail("Linear fill-up should not cause a collision");
                    }
                    // In case PartitionedFingerPrintGenerator and
                    // FingerPrintGenerator are used in performance tests, burn
                    // the same amount of cycles to obtain the next random like
                    // FPG does. puts is meaningless in the scope of PFPG
                    // anyway. It inserts up to a load factor of 1.
                    //puts += rnd.nextLong();
                    puts++;
                }
                fp += increment;
            } catch (final IOException e) {
                e.printStackTrace();
                Assert.fail("Unexpected");
            }
        }
        latch.countDown();
    }
}
