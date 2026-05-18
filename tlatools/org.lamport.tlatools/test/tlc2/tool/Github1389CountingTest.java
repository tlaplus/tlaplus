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

import java.io.IOException;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Regression test for https://github.com/tlaplus/tlaplus/issues/1389 exercising
 * the "counting safety property" use case -- the primary motivation for
 * permitting RECURSIVE operators at temporal level.
 *
 * <p>
 * A counting safety property bounds the number of times an event may occur. The
 * canonical pattern is "x is TRUE in at most n disjoint intervals",
 * equivalently "x transitions from FALSE to TRUE at most n times":
 * </p>
 *
 * <pre>
 *   RECURSIVE AtMost(_)
 *   AtMost(n) == IF n = 0 THEN []~x
 *                         ELSE [](x => [](~x => AtMost(n - 1)))
 *
 *   PROPERTY AtMost(4)
 *     \* -> [](x => [](~x => [](x => [](~x =>
 *     \*       [](x => [](~x => [](x => [](~x => []~x))))))))
 * </pre>
 *
 * <p>
 * Generalising the schema to an arbitrary bound is only natural via recursion;
 * before PR #1390, TLC rejected the operator outright with
 * {@link EC#TLC_LIVE_CANNOT_HANDLE_FORMULA}. The free-toggling spec
 * (<tt>x' \in BOOLEAN</tt>) admits behaviours that switch x arbitrarily often,
 * so {@code AtMost(4)} is violated and TLC must surface a counterexample whose
 * shortest witness is the ten-state prefix
 *
 * <pre>
 * FALSE -> TRUE -> FALSE -> TRUE -> FALSE -> TRUE -> FALSE -> TRUE -> FALSE -> TRUE
 * </pre>
 *
 * with five FALSE-to-TRUE transitions -- one more than the bound. Using
 * {@code AtMost(4)} (rather than {@code AtMost(1)}) makes the test sensitive to
 * regressions that prematurely terminate recursive expansion: shaving off any
 * single recursion step would yield a different (shorter or longer) shortest
 * counterexample, which the postcondition asserted below would catch.
 * </p>
 */
public class Github1389CountingTest extends ModelCheckerTestCase {

	public Github1389CountingTest() {
		// AtMost(4) expands to a pure safety formula whose
		// counterexample is a finite prefix, not a lasso, so TLC
		// reports VIOLATION_SAFETY rather than VIOLATION_LIVENESS.
		// The recursive operator still flows through the liveness
		// translator (otherwise expansion would not occur), so the
		// test still guards against TLC_LIVE_CANNOT_HANDLE_FORMULA
		// below.
		super("Github1389Counting", ExitStatus.VIOLATION_SAFETY);
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
	protected boolean runWithDebugger() {
		return false;
	}

	@Test
	public void testSpec() throws IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA));

		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_TEMPORAL_PROPERTY_VIOLATED, "CountAtMostFour"));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));

		// The shape of the counterexample is asserted by PostCondition in
		// the .tla module via TLCExt!CounterExample: a deterministic
		// ten-state prefix
		// <<1, [x |-> FALSE]>>, <<2, [x |-> TRUE]>>, ... ,
		// <<9, [x |-> FALSE]>>, <<10, [x |-> TRUE]>>
		// with x alternating, nine "Next" actions, and exactly the
		// number of states required to exhibit five FALSE-to-TRUE
		// transitions -- one more than the AtMost(4) bound. A
		// regression that prematurely terminates the recursive
		// expansion would produce a different number of states or a
		// different action sequence; TLC_POSTCONDITION_FALSE /
		// _EVALUATION_ERROR would fire below.
		assertFalse(recorder.recorded(EC.TLC_POSTCONDITION_FALSE));
		assertFalse(recorder.recorded(EC.TLC_POSTCONDITION_EVALUATION_ERROR));
	}
}
