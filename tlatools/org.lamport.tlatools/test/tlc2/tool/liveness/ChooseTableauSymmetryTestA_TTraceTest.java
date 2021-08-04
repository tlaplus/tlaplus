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

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.TLCStateInfo;

public class ChooseTableauSymmetryTestA_TTraceTest extends TTraceModelCheckerTestCase {

	public ChooseTableauSymmetryTestA_TTraceTest() {
		super(ChooseTableauSymmetryTestA.class, "symmetry", ExitStatus.VIOLATION_LIVENESS);
	}
	
	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "6", "5", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));

		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));

		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(7);
		// Trace prefix
		expectedTrace.add("arr = (a :> \"ready\" @@ b :> \"ready\")");
		expectedTrace.add("arr = (a :> \"busy\" @@ b :> \"ready\")");
		expectedTrace.add("arr = (a :> \"busy\" @@ b :> \"busy\")");
		expectedTrace.add("arr = (a :> \"done\" @@ b :> \"busy\")");
		expectedTrace.add("arr = (a :> \"ready\" @@ b :> \"busy\")");
		
		final List<String> expectedActions = new ArrayList<>();
		expectedActions.add(isExtendedTLCState()
				? "<_init line 23, col 5 to line 23, col 28 of module ChooseTableauSymmetryTestATTrace>"
				: TLCStateInfo.INITIAL_PREDICATE);
		expectedActions.add("<_next line 27, col 5 to line 33, col 33 of module ChooseTableauSymmetryTestATTrace>");
		expectedActions.add("<_next line 27, col 5 to line 33, col 33 of module ChooseTableauSymmetryTestATTrace>");
		expectedActions.add("<_next line 27, col 5 to line 33, col 33 of module ChooseTableauSymmetryTestATTrace>");
		expectedActions.add("<_next line 27, col 5 to line 33, col 33 of module ChooseTableauSymmetryTestATTrace>");
		
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);
		
		assertBackToState(3, "<_next line 27, col 5 to line 33, col 33 of module ChooseTableauSymmetryTestATTrace>");

	assertZeroUncovered();
	}
}
