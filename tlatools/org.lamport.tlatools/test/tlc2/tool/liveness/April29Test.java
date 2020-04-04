/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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
import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import org.junit.Ignore;
import org.junit.Test;

import tlc2.TLC;
import tlc2.output.EC;
import tlc2.tool.AbstractChecker;
import tlc2.tool.liveness.GraphNode.Transition;
import tlc2.util.BitVector;
import tlc2.util.LongVec;

/**
 * April29 and April29d exemplify how two different specifications have isomorph
 * state graphs under symmetry. Without symmetry, April29dTest does *not*
 * violate its liveness property. Under symmetry, TLC incorrectly finds a
 * violation and produces a bogus (identical to April29Test) counterexample.
 */
public class April29Test extends ModelCheckerTestCase {

	public April29Test() {
		super("April29MC", "symmetry");
	}
	
	@Test
	@Ignore("Ignored for as long as symmetry is incorrectly handled by TLC with liveness checking.")
	public void testSpec() throws IOException {
		// Assert TLC has found a temporal violation and a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(2);
		expectedTrace.add("/\\ x = a\n/\\ y = 0");
		expectedTrace.add("/\\ x = a\n/\\ y = 1");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

		assertStuttering(3);
		
		// Verify the nodes and arcs in the behavior graph in terms of nodes and arcs.
		final ILiveCheck liveCheck = (ILiveCheck) getField(AbstractChecker.class, "liveCheck",
				getField(TLC.class, "instance", tlc));
		assertEquals(1, liveCheck.getNumChecker());
		
		final ILiveChecker checker = liveCheck.getChecker(0);
		final DiskGraph graph = (DiskGraph) checker.getDiskGraph();
		graph.makeNodePtrTbl();
		assertEquals(2, graph.size()); // two nodes

		final LongVec initNodes = graph.getInitNodes();
		assertEquals(2, initNodes.size()); // <<fp,tidx>>, thus a single init state
		
		final int slen = checker.getSolution().getCheckState().length;
		assertEquals(0, slen);
		final int alen = checker.getSolution().getCheckAction().length;
		assertEquals(3, alen);
		
		final GraphNode init = graph.getNode(initNodes.elementAt(0));
		Set<Transition> transitions = init.getTransition(slen, alen);
		assertEquals(2, transitions.size()); // One self-loop and one successor
		
		// Remove self loop from init's transitions. The remaining transitions are
		// the true successors (here just a single).
		final List<Transition> outs = new ArrayList<Transition>();
		for (Transition t : transitions) {
			if (t.getFP() != init.stateFP) {
				outs.add(t);
			}
		}
		assertEquals(1, outs.size());
		
		final GraphNode successor = graph.getNode(outs.get(0).getFP());
		transitions = successor.getTransition(slen, alen);
		assertEquals(1, transitions.size());
		
		// Verify both outgoing transitions are self loops with the expected
		// action predicates. transitions is a Set and thus adding equal
		// instance does not increase the set's size.
		BitVector bv = new BitVector(alen + slen);
		bv.set(0);
		bv.set(2);
		transitions.add(new Transition(successor.stateFP, -1, bv));
		assertEquals(1, transitions.size());
	}
}
