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

import tlc2.output.EC;

public class NoSymmetryTableauModelCheckerTest extends ModelCheckerTestCase {

	public NoSymmetryTableauModelCheckerTest() {
		super("NoSymmetryLivenessTableauMC", "symmetry");
	}
	
	public void testSpec() {
		// ModelChecker intends to check liveness
		assertTrue(recorder.recordedWithStringValues(EC.TLC_LIVE_IMPLIED, "2"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_INIT_GENERATED1, "8", "s"));
		
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "5492", "1272", "0"));
		
		// Assert it has not found a temporal violation nor a counter example
		assertFalse(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertFalse(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		assertFalse(recorder.recorded(EC.TLC_STATE_PRINT2));
	}
}
