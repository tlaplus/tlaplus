/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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

package tlc2.tool.liveness;

import org.junit.Before;
import org.junit.Test;
import org.junit.experimental.categories.Category;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.tool.ModelCheckerTestCase;
import tlc2.tool.WorkerMonitor;
import util.LongTest;

import java.lang.management.ManagementFactory;
import java.lang.management.ThreadInfo;
import java.lang.management.ThreadMXBean;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * This test takes about four minutes with 32 cores on an EC2 cr1.8xlarge instance.
 * On a Thinkpad T430s it takes eight times as long and uses up 4GB of memory (see customBuild.xml).
 * <p>
 * The purpose of this test is to establish a thread contention baseline that TLC shows for
 * liveness checking (with and without tableaux). More precisely the time each TLC worker
 * thread spends in the WAITING and BLOCKED state must not exceed more than waitedRatio and
 * blockedRatio. The current values for waitedRatio and blockedRatio have been obtained empirically.
 */
public abstract class MultiThreadedSpecLongTest extends ModelCheckerTestCase {

    private final String statesGenerated;
    private final String distinctStatesGenerated;
    private final List<PerformanceResult> performanceResults = new ArrayList<>();
    private final CountDownLatch latch = new CountDownLatch(getNumberOfThreads());
    private final double waitedRatio;
    private final double blockedRatio;

    public MultiThreadedSpecLongTest(final String spec, final String path, final String statesGenerated, final String distinctStatesGenerated, final double blockedRatio, final double waitedRatio) {
        super(spec, path);
        this.statesGenerated = statesGenerated;
        this.distinctStatesGenerated = distinctStatesGenerated;
        this.blockedRatio = blockedRatio;
        this.waitedRatio = waitedRatio;
    }

    public MultiThreadedSpecLongTest(final String spec, final String path, final String[] extraArguments, final String statesGenerated, final String distinctStatesGenerated, final double blockedRatio, final double waitedRatio) {
        super(spec, path, extraArguments);
        this.statesGenerated = statesGenerated;
        this.distinctStatesGenerated = distinctStatesGenerated;
        this.blockedRatio = blockedRatio;
        this.waitedRatio = waitedRatio;
    }

    @Category(LongTest.class)
    @Test
    public void testSpec() throws InterruptedException {
        // ModelChecker has finished and generated the expected amount of states
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, statesGenerated, distinctStatesGenerated));

        // Assert it has found the temporal violation and also a counter example
        assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
        assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));

        // Assert the error trace
        assertTrue(recorder.recorded(EC.TLC_STATE_PRINT3));

        // Allow TLC worker threads to take 10 seconds to shutdown and report
        // their PerformanceResults to us. TLC's master thread has no reason to
        // wait for the final termination of all worker threads once it has
        // received the signal from one of them. After all the VM itself is
        // going to shutdown after TLC is done printing results.
        latch.await(10, TimeUnit.SECONDS);

        // Except as many results as we have started worker threads.
        //
        // If this assert fails, make sure that AspectJ is loaded and the
        // WorkerMonitorAspect is woven. This is done automatically by the ant
        // build (customBuild.xml) but not when this test is executed inside
        // Eclipse. AJDT (the AspectJ development tools) should not be a general
        // requirement to compile the tlatools/ project in Eclipse.
        //
        // If you ask why it uses AspectJ the first place... Rather than adding
        // API to the TLC code making in more and more complex just to test its
        // performance behavior, I deemed the extra test complexity caused by
        // AspectJ acceptable. We trade less complexity in program code with
        // higher complexity in test code.
        //
        // To run this test in Eclipse, install AJDT (http://eclipse.org/ajdt/),
        // convert the tlatools/ project into an AspectJ project via the
        // Package Explorers context menu and add
        // "-javaagent:${project_loc:tlatools}/lib/aspectjweaver-1.8.5.jar"
        // as a program argument to your JUnit launch config.
        //
        // If you get some but not all results, it's most certainly unrelated to
        // AspectJ and indicates a programming bug.
        assertEquals("PerfResult size is 0? => Is AspectJ load time weaving enabled?", getNumberOfThreads(),
                performanceResults.size());

        // None of the workers threads should have been blocked or waiting for
        // more than 25%
        for (final PerformanceResult result : performanceResults) {
            assertTrue(String.format("Blocked(%s): %.3f", result.threadName(), result.blockedRatio()),
                    result.blockedRatio() < blockedRatio);
            assertTrue(String.format("Waiting(%s): %.3f", result.threadName(), result.waitedRatio()),
                    result.waitedRatio() < waitedRatio);
        }
    }

    @Override
    @Before
    public void setUp() {
        // Set the threshold before TLC (periodically) checks liveness to
        // the largest possible value. This essentially stops TLC from checking
        // liveness during model checking and delays it until the end when one
        // final liveness check is run. We only then get deterministic behavior
        // needed by this test to e.g. check the number of states generated...
        TLCGlobals.livenessThreshold = Double.MAX_VALUE;

        final ThreadMXBean threadBean = ManagementFactory.getThreadMXBean();
        // Enable contention thread statistics to have the JVM measure
        // BlockedTime and WaitedTime.
        threadBean.setThreadContentionMonitoringEnabled(true);

        // Register a listener hot for the termination of the TLC worker
        // threads.
        // Using ThreadMXBean directly to lookup all threads after TLC has
        // finished has the potential that the JVM deletes the worker threads
        // before this test gets a chance to collect statistics.
        WorkerMonitor.addThreadListener(new WorkerMonitor.ThreadListener() {
            @Override
            public synchronized void terminated(final Thread thread, final long runningTime) {
                final ThreadInfo threadInfo = threadBean.getThreadInfo(thread.getId());
                final double d = threadInfo.getBlockedTime() / (runningTime * 1.0d);
                final double d2 = threadInfo.getWaitedTime() / (runningTime * 1.0d);
                performanceResults.add(new PerformanceResult(thread.getName(), d, d2));
                latch.countDown();
            }
        });

        super.setUp();
    }

    @Override
    protected int getNumberOfThreads() {
        // Run this test with as many threads possible to hopefully spot concurrency issues.
        return Runtime.getRuntime().availableProcessors();
    }

    private record PerformanceResult(String threadName, double blockedRatio, double waitedRatio) {


    }
}
