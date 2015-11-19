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

import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.rmi.RemoteException;

import org.junit.Before;

import tlc2.TLCGlobals;
import tlc2.output.MP;
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.MSBDiskFPSet;
import tlc2.tool.liveness.ModelCheckerTestCase;

public abstract class TLCServerTestCase extends ModelCheckerTestCase {

	public TLCServerTestCase(String spec) {
		super(spec);
	}

	public TLCServerTestCase(String spec, String path) {
		super(spec, path);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ModelCheckerTestCase#setUp()
	 */
	@Before
	public void setUp() {
		try {
			MP.setRecorder(recorder);
			
			// Never create checkpoints. They distort performance tests and are
			// of no use anyway.
			TLCGlobals.chkptDuration = 0;
			
			final String fqSpec = BASE_DIR + TEST_MODEL + path + File.separator + spec;
			final FPSetConfiguration fpSetConfig = new DummyFPSetConfig();
			final TLCApp app = new TLCApp(fqSpec, fqSpec, false, null, fpSetConfig);
			final TLCServer server = new TLCServer(app);
			server.modelCheck();
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}
	
	@SuppressWarnings("serial")
	private class DummyFPSetConfig extends FPSetConfiguration {

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.FPSetConfiguration#getImplementation()
		 */
		public String getImplementation() {
			return DummyFPSet.class.getName();
		}
	}
	
	@SuppressWarnings("serial")
	protected static class DummyFPSet extends MSBDiskFPSet {

		public DummyFPSet(FPSetConfiguration fpSetConfig) throws RemoteException {
			super(fpSetConfig);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.DiskFPSet#exit(boolean)
		 */
		public void exit(boolean cleanup) throws IOException {
			//ignore because superclass calls System.exit(0) but we want to check our assertions first.
		}
	}
}
