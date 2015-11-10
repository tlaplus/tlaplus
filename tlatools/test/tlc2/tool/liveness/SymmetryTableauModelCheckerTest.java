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

import static org.junit.Assert.assertTrue;

import org.junit.Ignore;
import org.junit.Test;
import tlc2.output.EC;

public class SymmetryTableauModelCheckerTest extends ModelCheckerTestCase {

	public SymmetryTableauModelCheckerTest() {
		super("SymmetryLivenessTableauMC", "symmetry");
	}
	
	@Test
	@Ignore("Ignored for as long as symmetry is incorrectly handled by TLC with liveness checking.")
	public void testSpec() {
		// ModelChecker intends to check liveness
		assertTrue(recorder.recordedWithStringValues(EC.TLC_LIVE_IMPLIED, "2"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_INIT_GENERATED2, "8", "s", "2"));
		
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "779", "168", "0"));

		// Assert it has found a temporal violation and a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		// The spec's 'NoVal' value is what violates symmetry.
		assertTrue(recorder.recordedWithStringValue(EC.GENERAL,
				"TLC threw an unexpected exception.\n" 
						+ "This was probably caused by an error in the spec or model.\n"
						+ "The error occurred when TLC was checking liveness.\n"
						+ "The exception was a tlc2.tool.EvalException\n"
						+ ": Failed to recover the next state from its fingerprint during\n"
						+ "liveness error trace re-construction. This indicates that the\n"
						+ "spec is in fact not symmetric (Please report a TLC bug if the\n"
						+ "spec is known to be symmetric)."));
	}
}
