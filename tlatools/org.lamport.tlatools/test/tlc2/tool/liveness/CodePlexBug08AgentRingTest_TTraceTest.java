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

/**
 * see http://tlaplus.codeplex.com/workitem/8
 */
public class CodePlexBug08AgentRingTest_TTraceTest extends TTraceModelCheckerTestCase {

	public CodePlexBug08AgentRingTest_TTraceTest() {
		super(CodePlexBug08AgentRingTest.class, "CodePlexBug08", ExitStatus.VIOLATION_SAFETY);
	}
	
	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "6", "6"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(4);
		expectedTrace.add("/\\ Agent = [Loc |-> 0, LastLoad |-> 0, ReadyToMove |-> TRUE, Task |-> 0]\n"
				   + "/\\ CanCreate = TRUE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 0] @@ 1 :> [Load |-> 0])");
		expectedTrace.add("/\\ Agent = [Loc |-> 0, LastLoad |-> 0, ReadyToMove |-> TRUE, Task |-> 0]\n"
				   + "/\\ CanCreate = TRUE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0])");
		expectedTrace.add("/\\ Agent = [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0]\n"
				   + "/\\ CanCreate = TRUE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 2] @@ 1 :> [Load |-> 0])");
		expectedTrace.add("/\\ Agent = [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0]\n"
				   + "/\\ CanCreate = TRUE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2])");
		// The two states below violate the liveness property [](~CanCreate /\
		// (\A i,j \in NodeRange : Nodes[i].Load = Nodes[j].Load) =>
		// [](Agent.Task = 0)). State 5 has CanCreate = FALSE and Task=0 and
		// state six changes Task back to 1.
		expectedTrace.add("/\\ Agent = [Loc |-> 1, LastLoad |-> 0, ReadyToMove |-> FALSE, Task |-> 0]\n"
				   + "/\\ CanCreate = FALSE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 2] @@ 1 :> [Load |-> 2])");
		expectedTrace.add("/\\ Agent = [Loc |-> 1, LastLoad |-> 1, ReadyToMove |-> TRUE, Task |-> 1]\n"
				   + "/\\ CanCreate = FALSE\n"
				   + "/\\ Nodes = (0 :> [Load |-> 2] @@ 1 :> [Load |-> 1])");

		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

		assertZeroUncovered();
	}
}
