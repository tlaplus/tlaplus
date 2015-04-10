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

package tlc2.tool.liveness.simulation;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class StutteringTest extends ModelCheckerTestCase {

	public StutteringTest() {
		super("MC", "CodePlexBug08", new String[] { "-simulate" });
	}

	public void testSpec() {
		// Simulation has finished and generated states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recorded(EC.TLC_STATS_SIMU));

		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));

		// Assert an error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));

		// The actual trace differs at each simulation due to its random
		// selection of the next state.

		// Assert the error trace contains a stuttering step at position 5
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT3));

		// Assert the error trace does NOT show back to state X
		assertFalse("Trace shows \"Back to state...\"", recorder.recorded(EC.TLC_BACK_TO_STATE));
	}
}
