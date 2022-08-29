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

package tlc2.tool.distributed;

import org.junit.Before;
import org.junit.runner.RunWith;
import org.junit.runners.BlockJUnit4ClassRunner;
import tlc2.TLCGlobals;
import tlc2.output.MP;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.MSBDiskFPSet;
import tlc2.tool.ModelCheckerTestCase;
import util.ToolIO;

import java.io.File;
import java.rmi.RemoteException;

import static org.junit.Assert.fail;

@RunWith(BlockJUnit4ClassRunner.class)
public abstract class TLCServerTestCase extends ModelCheckerTestCase {

    public TLCServerTestCase(final String spec) {
        super(spec);
    }

    public TLCServerTestCase(final String spec, final String path) {
        super(spec, path);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ModelCheckerTestCase#setUp()
     */
    @Override
    @Before
    public void setUp() {
        try {
            MP.setRecorder(recorder);

            // Never create checkpoints. They distort performance tests and are
            // of no use anyway.
            TLCGlobals.chkptDuration = 0;

            final String fqSpec = TEST_MODEL_PATH + path + File.separator + spec;
            final FPSetConfiguration fpSetConfig = new DummyFPSetConfig();
            ToolIO.setUserDir(TEST_MODEL_PATH + path + File.separator);
            final TLCApp app = new TLCApp(fqSpec, spec, false, null, fpSetConfig);

            try (final TLCServer server = new TLCServer(app)) {
                server.modelCheck();
            }

            //TODO Implement exit status for distributed TLC
            actualExitStatus = 0;
        } catch (final Exception e) {
            fail(e.getMessage());
        } finally {
            MP.unsubscribeRecorder(recorder);
        }
    }

    @SuppressWarnings("serial")
    private static class DummyFPSetConfig extends FPSetConfiguration {

        /* (non-Javadoc)
         * @see tlc2.tool.fp.FPSetConfiguration#getImplementation()
         */
        @Override
        public String getImplementation() {
            return DummyFPSet.class.getName();
        }
    }

    @SuppressWarnings("serial")
    protected static class DummyFPSet extends MSBDiskFPSet {

        public DummyFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
            super(fpSetConfig);
        }
    }
}
