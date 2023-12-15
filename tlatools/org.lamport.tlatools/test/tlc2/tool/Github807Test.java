/*******************************************************************************
 * Copyright (c) 2023 Microsoft Research. All rights reserved.
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
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github807Test extends ModelCheckerTestCase {

	public Github807Test() {
		super("Github807", new String[] { "-config", "Github807.tla" }, EC.ExitStatus.VIOLATION_SAFETY);
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
	protected boolean runWithDebugger() {
		// Force TLC to use TLCStateMut instead of TLCStateMutExt.  The latter has TLCStateMutExt#action.
		return false;
	}

	@Test
	public void testSpec() throws IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));

		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "3", "3", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "3"));

		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(7);
		// Trace prefix
		expectedTrace.add("x = 0");
		expectedTrace.add("x = 1");
		expectedTrace.add("x = 2");

		final List<String> expectedActions = new ArrayList<>();
		expectedActions.add(isExtendedTLCState() ? "<Init line 5, col 9 to line 5, col 13 of module Github807>"
				: TLCStateInfo.INITIAL_PREDICATE);
		expectedActions.add("<Add line 13, col 8 to line 13, col 15 of module Github807>");
		expectedActions.add("<Add line 13, col 8 to line 13, col 15 of module Github807>");

		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);

		// Assert POSTCONDITION.
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_FALSE));
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_EVALUATION_ERROR));
	}
}
