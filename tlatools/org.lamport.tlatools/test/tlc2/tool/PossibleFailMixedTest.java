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

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Exercises the _POSSIBLE feature with several predicates where only some are
 * never witnessed. This pins down the current error-reporting behavior so
 * regressions surface if it changes:
 * <ul>
 * <li>The failure is reported as {@link EC#TLC_POSTCONDITION_FALSE}.</li>
 * <li>The error identifies the first failing predicate in config order (here
 * {@code Unreachable}, a state-level predicate), not a shared placeholder like
 * {@code _Possible}.</li>
 * </ul>
 *
 * <p>
 * Note: {@link tlc2.tool.impl.Tool#checkPostConditionWithContext} returns on
 * the first failure, so later failing predicates (e.g. {@code BigJump}) are not
 * individually listed in the error output. If that behavior ever changes to
 * enumerate all failing possibles, this test needs to be updated accordingly.
 * </p>
 */
public class PossibleFailMixedTest extends ModelCheckerTestCase {

	public PossibleFailMixedTest() {
		super("PossibleFail", new String[] { "-config", "PossibleFailMixedTest.cfg" }, ExitStatus.VIOLATION_ASSUMPTION);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recorded(EC.TLC_POSTCONDITION_FALSE));
		// Predicates are evaluated in the order they appear in the config
		// (AtOne, AllDone, WrapAround, Unreachable, BigJump). The first three
		// are witnessed, so the first failure is Unreachable.
		assertTrue(recorder.recordedWithStringValueAt(EC.TLC_POSTCONDITION_FALSE, "Unreachable", 0));
	}
}
