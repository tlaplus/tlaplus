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

public class EmptySetEqStatesRcdTest extends ModelCheckerTestCase {

	// test-model/EmptySetEqStates.tla states what RcdSpec covers: a set of
	// records and the set of functions that denotes it, which TLC has to
	// fingerprint alike although it stores the one as a record and the other as
	// a function.
	public EmptySetEqStatesRcdTest() {
		super("EmptySetEqStates", new String[] { "-config", "EmptySetEqStatesRcd.cfg" });
	}

	@Override
	protected boolean checkDeadLock() {
		return true;
	}

	@Test
	public void testRcdSpec() {
		assertFalse(recorder.recorded(EC.TLC_DEADLOCK_REACHED));
		assertFalse(recorder.recorded(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));

		// [n1 : {"a"}] and [{"n1"} -> {"a"}] are one state, plus its successor.
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "3", "1", "0"));

		assertZeroUncovered();
	}

	@Override
	protected boolean noGenerateSpec() {
		return true; // not relevant for this test
	}
}
