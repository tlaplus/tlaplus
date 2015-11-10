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

import org.junit.Ignore;
import org.junit.Test;
import tlc2.output.EC;

public class SymmetryModelCheckerTest3a extends ModelCheckerTestCase {

	public SymmetryModelCheckerTest3a() {
		super("MCa", "symmetry");
	}
	
	@Test
	@Ignore("Ignored for as long as symmetry is incorrectly handled by TLC with liveness checking.")
	public void testSpec() {
		// Violates Prop1 of Spec1 which TLC correctly detects. However, it
		// produced a bogus counterexample. It does not use the symmetric state
		// that is actually supposed to be on the error trace. It uses the
		// smallest state under symmetry (the one all symmetric states get
		// mapped to).
		//
		// Spec1 and its action N1 more precisely can never make Prop1 eventually
		// _globally_ true. The second disjunct flips x's state forever. This
		// violation is correctly detected by TLC. However, due to the fact that
		// the x=b state is symmetry reduced and thus discarded from the
		// liveness graph causes the counter-example to incorrectly show a
		// violating state with x=a (where x=a logically does not violate
		// Prop1).
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "4", "2", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));

		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		assertNodeAndPtrSizes(72L, 32L);

		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(4);
		expectedTrace.add("/\\ x = a\n/\\ y = 0");
		expectedTrace.add("/\\ x = a\n/\\ y = 1"); // <= x changes after this state
		expectedTrace.add("/\\ x = b\n/\\ y = 0");
		expectedTrace.add("/\\ x = b\n/\\ y = 1");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
		
		assertBackToState(1);
		
		// Surprisingly enough, it turns out that LiveWorker#printTrace actually
		// generates a partially valid trace but simply fails to correctly print
		// it. It omits the final/last state with x=b from being printed. The
		// reason why printTrace(..) correctly generates the states is due to
		// the way the error trace gets generated. Starting from an init state,
		// it uses the predecessor and the successors fingerprint to generate
		// the successor state. For this model this means the error trace
		// contains the states <<(x=a, y=0), (x=a, y=1), (x=b, y=0)>>. The state
		// (x=b, y=0) is generated from its fingerprint f and its predecessor
		// state (x=a, y=1) AND the action N1. Since N1 mandates that x flips,
		// tool generates a state with x=b despite the declared symmetry.
	}
}
