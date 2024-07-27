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
public class CodePlexBug08AgentRingTest extends ModelCheckerTestCase {

	public CodePlexBug08AgentRingTest() {
		super("AgentRingMC", "CodePlexBug08", ExitStatus.VIOLATION_SAFETY);
	}
	
	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "171", "70"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));

		assertNodeAndPtrSizes(3552L, 1120L);
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(6);
		final List<String> expectedActions = new ArrayList<>();
		expectedActions.add("<Init line 50, col 3 to line 53, col 12 of module AgentRing>");
		expectedTrace.add("/\\ Agent = [Loc |-> 0, LastLoad |-> 0, ReadyToMove |-> TRUE, Task |-> 0]\n"
				   + "/\\ CanCreate = TRUE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 0] @@ 1 :> [Load |-> 0])");
		expectedActions.add("<CreateTasks line 82, col 3 to line 84, col 35 of module AgentRing>");
		expectedTrace.add("/\\ Agent = [Loc |-> 0, LastLoad |-> 0, ReadyToMove |-> TRUE, Task |-> 0]\n"
				   + "/\\ CanCreate = TRUE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0])");
		expectedActions.add("<Move line 58, col 3 to line 60, col 35 of module AgentRing>");
		expectedTrace.add("/\\ Agent = [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0]\n"
				   + "/\\ CanCreate = TRUE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0])");
		expectedActions.add("<CreateTasks line 82, col 3 to line 84, col 35 of module AgentRing>");
		expectedTrace.add("/\\ Agent = [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0]\n"
				   + "/\\ CanCreate = TRUE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2])");
		// The two states below violate the liveness property [](~CanCreate /\
		// (\A i,j \in NodeRange : Nodes[i].Load = Nodes[j].Load) =>
		// [](Agent.Task = 0)). State 5 has CanCreate = FALSE and Task=0 and
		// state six changes Task back to 1.
		expectedActions.add("<Stop line 78, col 3 to line 79, col 31 of module AgentRing>");
		expectedTrace.add("/\\ Agent = [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0]\n"
				   + "/\\ CanCreate = FALSE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2])");
		expectedActions.add("<LookAndAct line 63, col 3 to line 75, col 24 of module AgentRing>");
		expectedTrace.add("/\\ Agent = [Loc |-> 1, LastLoad |-> 1, ReadyToMove |-> TRUE, Task |-> 1]\n"
				   + "/\\ CanCreate = FALSE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 2] @@ 1 :> [Load |-> 1])");

		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);

		assertZeroUncovered();
		
		// Assert POSTCONDITION.
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_FALSE));
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_EVALUATION_ERROR));

		// Check that POSTCONDITION wrote the number of generated states to a TLCSet
		// register.
		final List<IValue> allValue = TLCGlobals.mainChecker.getAllValue(42);
		assertTrue(!allValue.isEmpty());
		assertEquals(IntValue.gen(171), allValue.get(0));
	}
}
