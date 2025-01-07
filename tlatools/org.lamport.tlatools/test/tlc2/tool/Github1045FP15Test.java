/*******************************************************************************
 * Copyright (c) 2025 Microsoft Corp. All rights reserved. 
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
package tlc2.tool;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github1045FP15Test extends ModelCheckerTestCase {
//8900da757ed1646710339a398a026496  15.tla.tmp
	public Github1045FP15Test() {
		super("Github1045", new String[] { "-config", "Github1045.tla", "-lncheck", "final", "-fp", "15" },
				ExitStatus.VIOLATION_LIVENESS);
	}

	// Deactivate a couple of unrelated features and their code paths.
	protected boolean doCoverage() {
		return false;
	}

	protected boolean runWithDebugger() {
		return false;
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "163", "27", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "6"));

		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));

		// The liveness property Convergence is violated because the spec does not
		// guarantee that there are (|Node \X Node| - |Node|)-many consecutive Gossip
		// actions.
		// It won't be sufficient to strengthening the fairness constraint to e.g.:
		//     \A n,m \in Node: WF_counter(Gossip(n,m))
		
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(5);
		final List<String> expectedActions = new ArrayList<>();
		expectedActions.add("<Initial predicate>");
		expectedTrace.add("counter = (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0))");

		expectedActions.add("<Increment(n2) line 17, col 3 to line 17, col 45 of module Github1045>");
		expectedTrace.add("counter = (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 1))");
		
		expectedActions.add("<Increment(n1) line 17, col 3 to line 17, col 45 of module Github1045>");
		expectedTrace.add("counter = (n1 :> (n1 :> 1 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 1))");
		
		expectedActions.add("<Gossip(n2,n1) line 20, col 3 to line 25, col 5 of module Github1045>");
		expectedTrace.add("counter = (n1 :> (n1 :> 1 @@ n2 :> 1) @@ n2 :> (n1 :> 0 @@ n2 :> 1))");
		
		expectedActions.add("<Increment(n2) line 17, col 3 to line 17, col 45 of module Github1045>");
		expectedTrace.add("counter = (n1 :> (n1 :> 1 @@ n2 :> 1) @@ n2 :> (n1 :> 0 @@ n2 :> 2))");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);

		// The BackToState step is weird but correct; it is the combination of a
		// Gossip(n2,n1) action and a VIEW reduction. The t in the s -Gossip(n2,n1)-> t
		// action is equal to: 
		//   counter=(n1 :> (n1 :> 1 @@ n2 :> 1) @@ n2 :> (n1 :> 1 @@ n2 :> 2)
		// This value is reduced to:
		//   counter=(n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 1))
		assertBackToState(2, "<Gossip(n1,n2) line 20, col 3 to line 25, col 5 of module Github1045>");
	}
}
