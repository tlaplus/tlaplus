/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved. 
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

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class EmptySetEqStatesTest extends ModelCheckerTestCase {

	// test-model/EmptySetEqStates.tla states what Spec covers. Its initial
	// predicate ends up in Value#fingerPrint, its next-state relation in
	// Value#equals.
	public EmptySetEqStatesTest() {
		super("EmptySetEqStates");
	}

	@Override
	protected boolean checkDeadLock() {
		// A spurious deadlock is one of the two symptoms this test is after, the
		// number of distinct states the other.
		return true;
	}

	@Test
	public void testSpec() {
		assertFalse(recorder.recorded(EC.TLC_DEADLOCK_REACHED));
		assertFalse(recorder.recorded(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));

		// The 34 sets of Forms fingerprint as the four values they denote, plus one
		// successor per state.
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "38", "4", "0"));

		assertZeroUncovered();
	}

	@Override
	protected boolean noGenerateSpec() {
		return true; // not relevant for this test
	}
}
