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

public abstract class SuccessfulSimulationTestCase extends ModelCheckerTestCase {

	public SuccessfulSimulationTestCase(String spec) {
		super(spec);
	}

	public SuccessfulSimulationTestCase(String spec, String path) {
		super(spec, path);
	}

	public SuccessfulSimulationTestCase(String spec, String path, String[] extraArguments) {
		super(spec, path, extraArguments);
	}
	
	public void testSpec() {
		// Simulation must *NOT* show a counterexample. Regular model-checking
		// shows that the liveness property holds.
		//
		// Since simulation runs forever until it either finds a counterexample
		// or it is manually stopped, we can only keep it running for a fixed
		// amount of time and stop it afterwards.

		// Finished...
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		// No temporal violation
		assertFalse(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		// No counterexample
		assertFalse(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		// No trace
		assertFalse(recorder.recorded(EC.TLC_STATE_PRINT2));
		// Does not stutter
		assertFalse(recorder.recorded(EC.TLC_STATE_PRINT3));
		// No back loop to init state
		assertFalse(recorder.recorded(EC.TLC_STATE_PRINT2));
	}
}
