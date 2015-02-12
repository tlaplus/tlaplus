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

import java.io.File;

import junit.framework.TestCase;
import tlc2.TLC;
import tlc2.TestMPRecorder;
import tlc2.output.MP;
import util.ToolIO;

public abstract class ModelCheckerTestCase extends TestCase {

	private static final String TEST_MODEL = "test-model" + File.separator;
	
	private String path = "";
	private final String spec;
	protected final TestMPRecorder recorder = new TestMPRecorder();


	public ModelCheckerTestCase(String spec) {
		this.spec = spec;
	}

	public ModelCheckerTestCase(String spec, String path) {
		this(spec);
		this.path = path;
	}
	
	public void setUp() {
		try {
			// TEST_MODEL is where TLC should look for user defined .tla files
			ToolIO.setUserDir(TEST_MODEL + path);
			
			MP.setRecorder(recorder);
			
			final TLC tlc = new TLC();
			// * We want *no* deadlock checking to find the violation of the
			// temporal formula
			// * We use a single worker to simplify debugging by taking out
			// threading
			// * MC is the name of the TLA+ specification to be checked (the file
			// is placed in TEST_MODEL
			final String[] args = { "-deadlock", "-workers", "1", spec };
			tlc.handleParameters(args);
			
			// Run the ModelChecker
			tlc.process();
			
		} catch (Exception e) {
			fail();
		}
	}

}
