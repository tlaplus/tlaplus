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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.value.IValue;
import tlc2.value.impl.IntValue;

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
		final List<String> expectedTrace = new ArrayList<String>(17);
		final List<String> expectedActions = new ArrayList<String>();
		//1
		expectedActions.add("<Init line 50, col 9 to line 54, col 44 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> FALSE)\n" 
						+ "/\\ pc = (A :> \"ncs\" @@ B :> \"ncs\")");
		//2
		expectedActions.add("<ncs(A) line 56, col 14 to line 58, col 51 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n"
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> FALSE)\n"
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"ncs\")");
		//3
		expectedActions.add("<ncs(B) line 56, col 14 to line 58, col 51 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n"
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> FALSE)\n"
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e1\")");
		//4
		expectedActions.add("<e1(B) line 60, col 13 to line 64, col 29 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {A})\n"
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e2\")");
		//5
		expectedActions.add("<e2(B) line 66, col 13 to line 74, col 21 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e3\")");
		//6
		expectedActions.add("<e3(B) line 76, col 13 to line 82, col 50 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e2\")");
		//7
		expectedActions.add("<e2(B) line 66, col 13 to line 74, col 21 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"cs\")");
		//8 (Loops back to)
		expectedActions.add("<e1(A) line 60, col 13 to line 64, col 29 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {B} @@ B :> {})\n" 
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e2\" @@ B :> \"cs\")");
		//9
		expectedActions.add("<e2(A) line 66, col 13 to line 74, col 21 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e3\" @@ B :> \"cs\")");
		//10
		expectedActions.add("<cs(B) line 99, col 13 to line 102, col 50 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e3\" @@ B :> \"f\")");
		//11
		expectedActions.add("<e3(A) line 76, col 13 to line 82, col 50 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e4\" @@ B :> \"f\")");
		//12
		expectedActions.add("<f(B) line 104, col 12 to line 107, col 46 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> FALSE)\n" 
						+ "/\\ pc = (A :> \"e4\" @@ B :> \"ncs\")");
		//13
		expectedActions.add("<ncs(B) line 56, col 14 to line 58, col 51 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> FALSE)\n" 
						+ "/\\ pc = (A :> \"e4\" @@ B :> \"e1\")");
		//14
		expectedActions.add("<e4(A) line 84, col 13 to line 87, col 47 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> FALSE)\n" 
						+ "/\\ pc = (A :> \"e5\" @@ B :> \"e1\")");
		//15
		expectedActions.add("<e5(A) line 89, col 13 to line 92, col 50 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> FALSE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e1\")");
		//16
		expectedActions.add("<e1(B) line 60, col 13 to line 64, col 29 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {A})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e2\")");
		//17
		expectedActions.add("<e2(B) line 66, col 13 to line 74, col 21 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e3\")");
		//18
		expectedActions.add("<e3(B) line 76, col 13 to line 82, col 50 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e2\")");
		//19
		expectedActions.add("<e1(A) line 60, col 13 to line 64, col 29 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {B} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e2\" @@ B :> \"e2\")");
		//20
		expectedActions.add("<e2(A) line 66, col 13 to line 74, col 21 of module OneBitMutex>");
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e3\" @@ B :> \"e2\")");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);

		assertBackToState(9, "<e2(B) line 66, col 13 to line 74, col 21 of module OneBitMutex>");

		assertUncovered("line 80, col 38 to line 80, col 69 of module OneBitMutex: 0\n"
				+ "line 96, col 16 to line 96, col 47 of module OneBitMutex: 0\n"
				+ "line 97, col 16 to line 97, col 50 of module OneBitMutex: 0");

		// Assert POSTCONDITION.
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_FALSE));
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_EVALUATION_ERROR));

		// Check that POSTCONDITION wrote the number of generated states to a TLCSet
		// register.
		final List<IValue> allValue = TLCGlobals.mainChecker.getAllValue(42);
		assertTrue(!allValue.isEmpty());
		assertEquals(IntValue.gen(244), allValue.get(0));
	}
}
