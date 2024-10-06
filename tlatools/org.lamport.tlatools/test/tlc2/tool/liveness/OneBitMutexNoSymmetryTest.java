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

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;

public class OneBitMutexNoSymmetryTest extends ModelCheckerTestCase {

	public OneBitMutexNoSymmetryTest() {
		super("OneBitMutexNoSymmetryMC", "symmetry" + File.separator + "OneBitMutex", ExitStatus.VIOLATION_LIVENESS);
	}
	
	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "244", "127", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));

		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		assertNodeAndPtrSizes(11700L, 3728L);

		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));

		assertUncovered("line 80, col 38 to line 80, col 69 of module OneBitMutex: 0\n"
				+ "line 96, col 16 to line 96, col 47 of module OneBitMutex: 0\n"
				+ "line 97, col 16 to line 97, col 50 of module OneBitMutex: 0");

		// Assert POSTCONDITION.
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_FALSE));
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_EVALUATION_ERROR));

		// Check that POSTCONDITION wrote the number of generated states to a TLCSet
		// register.
//		final List<IValue> allValue = TLCGlobals.mainChecker.getAllValue(42);
//		assertTrue(!allValue.isEmpty());
//		assertEquals(IntValue.gen(244), allValue.get(0));
	}
}
