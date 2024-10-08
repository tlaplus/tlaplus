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
public class CodePlexBug08EWD840FL1Test extends ModelCheckerTestCase {

	public CodePlexBug08EWD840FL1Test() {
		super("EWD840MC1", "CodePlexBug08", ExitStatus.VIOLATION_LIVENESS);
	}
	
	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "15986", "1566", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		assertNodeAndPtrSizes(7560068L, 279616L);
		
		// Error trace is asserted in the post condition.

		assertZeroUncovered();
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(10);
		final List<String> expectedActions = new ArrayList<String>();
		expectedActions.add("<Init line 21, col 3 to line 24, col 21 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 0\n"
				+ "/\\ tcolor = \"black\"");
		expectedActions.add("<InitiateProbe line 30, col 3 to line 35, col 43 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<SendMsg(3) line 61, col 3 to line 65, col 31 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<SendMsg(2) line 61, col 3 to line 65, col 31 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<SendMsg(1) line 61, col 3 to line 65, col 31 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<SendMsg(1) line 61, col 3 to line 65, col 31 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<SendMsg(2) line 61, col 3 to line 65, col 31 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<Deactivate(0) line 69, col 3 to line 71, col 38 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<Deactivate(1) line 69, col 3 to line 71, col 38 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<SendMsg(2) line 61, col 3 to line 65, col 31 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<Deactivate(2) line 69, col 3 to line 71, col 38 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<Deactivate(3) line 69, col 3 to line 71, col 38 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<PassToken(3) line 47, col 3 to line 52, col 43 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 2\n"
				+ "/\\ tcolor = \"white\"");
		expectedActions.add("<PassToken(2) line 47, col 3 to line 52, col 43 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 1\n"
				+ "/\\ tcolor = \"black\"");
		expectedActions.add("<SendMsg(1) line 61, col 3 to line 65, col 31 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 1\n"
				+ "/\\ tcolor = \"black\"");
		expectedActions.add("<Deactivate(1) line 69, col 3 to line 71, col 38 of module EWD840>");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 1\n"
				+ "/\\ tcolor = \"black\"");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);

		assertBackToState(1, "<PassToken(1) line 47, col 3 to line 52, col 43 of module EWD840>");
		
		// Check that POSTCONDITION wrote the number of generated states to a TLCSet
		// register.
		final List<IValue> allValue = TLCGlobals.mainChecker.getAllValue(42);
		assertTrue(!allValue.isEmpty());
		assertEquals(IntValue.gen(15986), allValue.get(0));
	}
}
