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
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Regression test for https://github.com/tlaplus/tlaplus/issues/1161 Soundness
 * check: verifies that TLC correctly detects a violation when a RECURSIVE
 * operator argument is passed through an INSTANCEd Double-style wrapper. This
 * exercises both the getVal fix (operator argument binding) and the
 * getInRecursive() guard (recursive operators are not syntactically expanded
 * by astToLive but evaluated at runtime). The property [](RecViolated(s)) is
 * violated because RecViolated returns FALSE for s >= 5.
 */
public class Github1161ViolatedTest extends ModelCheckerTestCase {

	public Github1161ViolatedTest() {
		super("Github1161", new String[] { "-config", "Github1161Violated.cfg" }, ExitStatus.VIOLATION_SAFETY);
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

	@Override
	protected boolean doCoverage() {
		return false;
	}

	@Test
	public void testSpec() throws IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA));

		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));

		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<>(6);
		expectedTrace.add("s = 0");
		expectedTrace.add("s = 1");
		expectedTrace.add("s = 2");
		expectedTrace.add("s = 3");
		expectedTrace.add("s = 4");
		expectedTrace.add("s = 5");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
	}
}
