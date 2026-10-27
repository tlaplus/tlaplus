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

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;

// See https://github.com/tlaplus/tlaplus/issues/1497
public class Github1497Test extends ModelCheckerTestCase {

	public Github1497Test() {
		// Every trace is x = 0, x = 1, x = 1, ..., so the first trace has to
		// expose the violation.
		super("Github1497", new String[] { "-simulate", "num=10", "-depth", "10" },
				ExitStatus.VIOLATION_LIVENESS);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));

		assertTrue(recorder.recordedWithStringValue(EC.TLC_TEMPORAL_PROPERTY_VIOLATED, "Prop"));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));

		final List<String> expectedTrace = new ArrayList<>(2);
		expectedTrace.add("x = 0");
		expectedTrace.add("x = 1");
		final List<String> expectedActions = new ArrayList<>(2);
		expectedActions.add("<Init line 4, col 9 to line 4, col 13 of module Github1497>");
		expectedActions.add("<Next line 5, col 9 to line 5, col 14 of module Github1497>");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);

		assertStuttering(3);
	}
}
