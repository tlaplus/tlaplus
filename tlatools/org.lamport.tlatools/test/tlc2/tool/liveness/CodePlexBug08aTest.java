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

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.value.IValue;
import tlc2.value.impl.IntValue;

/**
 * see http://tlaplus.codeplex.com/workitem/8
 */
public class CodePlexBug08aTest extends ModelCheckerTestCase {

	public CodePlexBug08aTest() {
		super("MCa", "CodePlexBug08", ExitStatus.VIOLATION_LIVENESS);
	}
	
	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "18", "11", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		assertNodeAndPtrSizes(816L, 352L);
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(4);
		final List<String> expectedActions = new ArrayList<>();
		expectedActions.add("<Init line 15, col 9 to line 15, col 35 of module CodeplexBug8>");
		expectedTrace.add("/\\ b = FALSE\n/\\ x = 1");
		expectedActions.add("<B line 11, col 6 to line 13, col 18 of module CodeplexBug8>");
		expectedTrace.add("/\\ b = TRUE\n/\\ x = 2");
		expectedActions.add("<A line 6, col 6 to line 9, col 19 of module CodeplexBug8>");
		expectedTrace.add("/\\ b = FALSE\n/\\ x = 2");
		expectedActions.add("<B line 11, col 6 to line 13, col 18 of module CodeplexBug8>");
		expectedTrace.add("/\\ b = TRUE\n/\\ x = 3");
		expectedActions.add("<A line 6, col 6 to line 9, col 19 of module CodeplexBug8>");
		expectedTrace.add("/\\ b = FALSE\n/\\ x = 3");
		expectedActions.add("<B line 11, col 6 to line 13, col 18 of module CodeplexBug8>");
		expectedTrace.add("/\\ b = TRUE\n/\\ x = 4");
		expectedActions.add("<A line 6, col 6 to line 9, col 19 of module CodeplexBug8>");
		expectedTrace.add("/\\ b = FALSE\n/\\ x = 4");
		expectedActions.add("<B line 11, col 6 to line 13, col 18 of module CodeplexBug8>");
		expectedTrace.add("/\\ b = TRUE\n/\\ x = 5");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);
		
		// Assert the error trace contains a stuttering step at position 5
		assertStuttering(9);

		assertZeroUncovered();
		
		// Assert POSTCONDITION.
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_FALSE));
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_EVALUATION_ERROR));

		// Check that POSTCONDITION wrote the number of generated states to a TLCSet
		// register.
		final List<IValue> allValue = TLCGlobals.mainChecker.getAllValue(42);
		assertTrue(!allValue.isEmpty());
		assertEquals(IntValue.gen(18), allValue.get(0));
	}
}
