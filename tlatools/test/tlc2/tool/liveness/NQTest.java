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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;

import org.junit.Ignore;
import org.junit.Test;

import tlc2.output.EC;

public class NQTest extends ModelCheckerTestCase {

	public NQTest() {
		super("MC", "symmetry" + File.separator + "NQ");
	}
	
	/*
	 * WRT @Ignore:
	 * Without symmetry defined, TLC finds no counterexample. With symmetry,
	 * which is the case for this test, TLC incorrectly finds a counterexample
	 * which it subsequently fails to recreate. In the end, this causes TLC to
	 * claim that the spec is not symmetric.
	 * 
	 * So why does TLC think the PossibleErrorModel is P-Satisfiable and
	 * consequently tries to produce a counterexample?
	 */
	@Test
	@Ignore("Ignored for as long as symmetry is incorrectly handled by TLC with liveness checking.")
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "1049", "363", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));

		// Assert it has *not* found a temporal violation and a counter example
		assertFalse(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertFalse(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		// Assert *no* error trace
		assertFalse(recorder.recorded(EC.TLC_STATE_PRINT2));
	}
}
