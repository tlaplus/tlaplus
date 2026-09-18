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
package tlc2.tool.liveness;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;

/**
 * Regression for https://github.com/tlaplus/model-checker-hardening/issues/137
 */
public class InitialLivenessEvaluationErrorTest extends ModelCheckerTestCase {

	public InitialLivenessEvaluationErrorTest() {
		super("InitialLivenessEvaluationError", ExitStatus.ERROR_CONFIG_PARSE);
	}

	@Override
	protected void assertExitStatus() {
		assertTrue("Expected a configuration error or invariant violation, but TLC returned " + actualExitStatus,
				actualExitStatus == ExitStatus.ERROR_CONFIG_PARSE
						|| actualExitStatus == ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.TLC_SUCCESS));

		if (actualExitStatus == ExitStatus.VIOLATION_SAFETY) {
			assertTrue(recorder.recordedWithStringValue(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, "Inv"));
			assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
			assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), Arrays.asList("x = 0", "x = 1"));
		} else {
			assertTrue(recorder.recorded(EC.TLC_INITIAL_STATE)
					|| recorder.recorded(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_LIVE));
			// The initial evaluation error prevents TLC from reaching Inv's violation.
			assertFalse(recorder.recorded(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR));
			assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "1", "1", "1"));
		}
	}

	@Override
	protected boolean runWithDebugger() {
		return false;
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Override
	protected boolean doDump() {
		return false;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}
}
