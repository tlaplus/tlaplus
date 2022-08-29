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
package tlc2.tool.distributed;

import org.junit.After;
import org.junit.Assert;
import org.junit.Assume;
import org.junit.Before;
import tlc2.TestMPRecorder;
import tlc2.output.MP;
import tlc2.tool.CommonTestCase;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.distributed.fp.DistributedFPSet;

import java.util.List;
import java.util.concurrent.CountDownLatch;

import static org.junit.Assert.*;

public abstract class DistributedTLCTestCase extends CommonTestCase {

    protected final String[] arguments;
    protected final int fpSets;


    public DistributedTLCTestCase(final String spec, final String path, final String[] args) {
        this(spec, path, args, 0);
    }

    public DistributedTLCTestCase(final String spec, final String path, final String[] args, final int fpSets) {
        super(new TestMPRecorder());
        this.arguments = new String[args.length + 1];
        this.arguments[this.arguments.length - 1] = path + spec; // Add path to additional arguments
        System.arraycopy(args, 0, arguments, 0, args.length);

        this.fpSets = fpSets;
    }

    protected boolean isExtendedTLCState() {
        return true;
    }

    /**
     * Asserts that the actual trace and the expected error trace are equal.
     *
     * @param actual        The actual trace as recorded by {@link tlc2.TestMPRecorder}.
     * @param expectedTrace The expected trace.
     */
    protected void assertTraceWith(final List<Object> actual, final List<String> expectedTrace) {
        assertEquals(expectedTrace.size(), actual.size());
        for (int i = 0; i < expectedTrace.size(); i++) {
            final Object[] objs = (Object[]) actual.get(i);
            final TLCStateInfo stateInfo = (TLCStateInfo) objs[0];
            final String info = (String) stateInfo.info;
            if (i == 0 && !isExtendedTLCState()) {
                // The first state has to be an initial state.
                assertEquals("<Initial predicate>", info);
            } else {
                // ... all others are reachable via an action.
                //TODO: Assert actual action names.
                assertNotEquals("<Initial predicate>", info);
                assertFalse(info.startsWith("<Action"));
            }
            assertEquals(expectedTrace.get(i),
                    stateInfo.toString().trim()); // trimmed to remove any newlines or whitespace
            assertEquals(i + 1, objs[1]);
        }
    }

    @Before
    public void setUp() {
        Assume.assumeTrue("DistributedTLCTestCase broken with OffHeapDiskFPSet.", false);
        // Remember the original security manager and have it replaced with this
        // custom one. Contrary to the original, this security manager
        // intercepts calls to System.exit(int) and throws an exception instead
        // of terminating the VM. This is done to prevent TLCWorker/TLCServer/...
        // from terminating the JUnit test itself. To allow the JUnit test to
        // later terminate the VM after test completion, we have to reinstate
        // the original security manager again (see tearDown).

        MP.setRecorder(recorder);

        // Wait for all processes to terminate before the setup itself is done
        final CountDownLatch latch = new CountDownLatch(fpSets + 2);

        // Workers
        new Thread(() -> {
            try {
                TLCWorker.main(new String[]{"localhost"});
            } catch (final Exception e) {
                e.printStackTrace();
            } finally {
                latch.countDown();
            }
        }, "Worker").start();

        // master
        new Thread(() -> {
            try {
                System.setProperty(TLCServer.class.getName() + ".expectedFPSetCount", Integer.toString(fpSets));
                TLCServer.handleArgs(arguments);
            } catch (final Exception e) {
                e.printStackTrace();
            } finally {
                latch.countDown();
            }
        }, "Master").start();

        // FPSet
        if (fpSets > 0) {
            new Thread(() -> {
                try {
                    DistributedFPSet.main(new String[]{"localhost"});
                } catch (final Exception e) {
                    e.printStackTrace();
                } finally {
                    latch.countDown();
                }
            }, "FPSet").start();
        }

        try {
            latch.await();
        } catch (final InterruptedException e) {
            Assert.fail();
        }
    }

    @After
    public void tearDown() {
        MP.unsubscribeRecorder(recorder);
    }
}
