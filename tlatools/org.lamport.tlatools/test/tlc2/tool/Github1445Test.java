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
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Regression test for https://github.com/tlaplus/tlaplus/issues/1445
 *
 * Tool#getActions evaluates constant-level action arguments and values bound by
 * a top-level \E once, and stores them in the context of the Action that all
 * workers share. Likewise, SpecProcessor and Liveness bind the values of a
 * bounded quantification in properties and fairness conditions. Workers race to
 * normalize (sort in place) these values when they enumerate or fingerprint
 * them. The race drops elements from enumerated sets (missing states and bogus
 * violations of Inv, Live, and Fair), yields inconsistent fingerprints for lazy
 * sets (extra states), and duplicates elements in the domain of lazy functions
 * (a bogus error).
 */
public class Github1445Test extends ModelCheckerTestCase {

	public Github1445Test() {
		super("Github1445", ExitStatus.SUCCESS);
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Override
	protected boolean doDump() {
		return false;
	}

	@Override
	protected int getNumberOfThreads() {
		// The race requires multiple workers.
		return 8;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		// 8 initial states, 3 * 8 * 2048 states from the Enum actions, and 2 states
		// from the Assign actions. Each of the latter 49154 states also generates
		// itself by stuttering.
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "98330", "49162", "0"));
	}
}
