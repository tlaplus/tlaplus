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

import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;

import tlc2.output.EC;

/**
 * May09Test and its counterpart May09dTest prove that the algorithm with
 * redundant arcs with different action predicate labels in the liveness graph
 * does not work even when liveness properties containing conjuncts over the
 * elements of the symmetry set are rewritten to a disjunct and out-arcs are
 * counted (compare to {@link April29Test} and {@link April29dTest}).
 * 
 * <pre>
 *	[]<>P(a) /\ []<>P(b) rewritten to: []<>P(a) \/ []<>P(b)
 * </pre>
 * 
 * (where P is either a State or Action predicate and a,b are all elements of
 * the symmetry set)
 * 
 * Trying to deduce []<>P(b) from the occurrence of []<>P(a) (or vice versa)
 * fails because the two specs (Spec & SpecD) under symmetry produce the same
 * state graph. Without symmetry, Spec does not satisfy []<>P(a) /\ []<>P(b),
 * only SpecD does. Under symmetry, a version of TLC that does not rewrite the
 * liveness property finds the bogus counterexample for SpecD.  
 * 
 * A yet unexplored research hypothesis is, that labeling all arcs with the
 * permutation that the to-state represents in the liveness graph. This information
 * would allow us to distinguish the graphs of May09 and May09d.
 */
public class May09Test extends ModelCheckerTestCase {

	public May09Test() {
		super("May09MC", "symmetry");
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
		expectedTrace.add("/\\ x = a\n/\\ y = 2");
		expectedTrace.add("/\\ x = a\n/\\ y = 3");
		expectedTrace.add("/\\ x = a\n/\\ y = 4");
		expectedTrace.add("/\\ x = a\n/\\ y = 5");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

		assertBackToState(2, "<Action line 19, col 10 to line 21, col 18 of module May09>");
	}
}
