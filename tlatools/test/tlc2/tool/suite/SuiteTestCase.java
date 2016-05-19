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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public abstract class SuiteTestCase extends ModelCheckerTestCase {

	private String initStates = "1";
	private String leftStates = "0";
	private String distinctStates = "1";
	private String stateGenerated = "2";
	
	public SuiteTestCase() {
		super("setBySetUp", "suite");
	}

	public SuiteTestCase(String stateGenerated, String distinctStates, String leftStates, String initStates) {
		this();
		this.stateGenerated = stateGenerated;
		this.distinctStates = distinctStates;
		this.leftStates = leftStates;
		this.initStates = initStates;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ModelCheckerTestCase#setUp()
	 */
	public void setUp() {
		// Set spec name to the name of the unit tests
		spec = getClass().getSimpleName().toLowerCase();
		
		super.setUp();
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, stateGenerated, distinctStates, leftStates));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, initStates));
		assertFalse(recorder.recorded(EC.GENERAL));
	}
}
