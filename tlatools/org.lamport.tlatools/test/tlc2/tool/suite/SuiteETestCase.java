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

package tlc2.tool.suite;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.TestPrintStream;
import util.ToolIO;

public abstract class SuiteETestCase extends ModelCheckerTestCase {

	private final TestPrintStream testPrintStream = new TestPrintStream();

	public SuiteETestCase() {
		this(ExitStatus.SUCCESS);
	}

	public SuiteETestCase(int exitStatus) {
		super("setBySetUp", "suite", exitStatus);
	}
	
	public SuiteETestCase(String[] params) {
		this(params, ExitStatus.SUCCESS);
	}

	public SuiteETestCase(String[] params, int exitStatus) {
		super("setBySetUp", "suite", params, exitStatus);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ModelCheckerTestCase#setUp()
	 */
	public void setUp() {
		// Set spec name to the name of the unit tests
		spec = getClass().getSimpleName().toLowerCase();
		
		// Intercept tool out to check SANY parser errors
		ToolIO.out = testPrintStream;
		ToolIO.err = testPrintStream;
		
		super.setUp();
	}
	
	
	protected void assertSubstring(String substring) {
		testPrintStream.assertSubstring(substring);
	}
}
