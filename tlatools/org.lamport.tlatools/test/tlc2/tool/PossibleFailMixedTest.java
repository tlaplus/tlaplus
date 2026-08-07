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
 * never witnessed ({@code Unreachable} and {@code BigJump}). The failure must
 * be reported as {@link EC#TLC_POSSIBLE_UNWITNESSED} and must name one of the
 * unwitnessed predicates rather than a shared placeholder like
 * {@code _Possible}.
 *
 * <p>
 * Which one TLC names is not a guarantee of the feature: _POSSIBLE leaves it
 * unspecified, because
 * {@link tlc2.tool.impl.Tool#checkPostConditionWithContext} reports the first
 * predicate whose check fails and the order in which the checks run is an
 * implementation detail. The assertion below pins down today's outcome
 * ({@code Unreachable}) so that a change becomes visible rather than silent; it
 * is not a contract, so reordering the checks may legitimately require updating
 * the expected name here.
 * </p>
 *
 * <p>
 * Only one predicate is named either way. The record of witness counts printed
 * before the error is what identifies every unwitnessed predicate, including
 * {@code BigJump}.
 * </p>
 */
public class PossibleFailMixedTest extends ModelCheckerTestCase {

	public PossibleFailMixedTest() {
		super("PossibleFail", new String[] { "-config", "PossibleFailMixedTest.cfg" }, ExitStatus.VIOLATION_ASSUMPTION);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recorded(EC.TLC_POSSIBLE_UNWITNESSED));
		// Unreachable and BigJump are both unwitnessed; TLC currently names the
		// former. See the class comment: this pins down behavior, not a contract.
		assertTrue(recorder.recordedWithStringValueAt(EC.TLC_POSSIBLE_UNWITNESSED, "Unreachable", 0));
	}
}
