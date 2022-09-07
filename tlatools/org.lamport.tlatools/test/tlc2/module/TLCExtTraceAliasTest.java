/*******************************************************************************
 * Copyright (c) 2022 Microsoft Research. All rights reserved. 
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
package tlc2.module;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class TLCExtTraceAliasTest extends ModelCheckerTestCase {

	public TLCExtTraceAliasTest() {
		super("TLCExtTrace", new String[] {"-config", "TLCExtTraceAlias.cfg"}, EC.ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void test() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "7"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "7", "7", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		
		// Assert the correct trace.
		final List<String> expectedTrace = new ArrayList<String>(7);
		expectedTrace.add("/\\ x = 1\n/\\ t = <<[x |-> 1]>>");
		expectedTrace.add("/\\ x = 2\n/\\ t = <<[x |-> 1], [x |-> 2]>>");
		expectedTrace.add("/\\ x = 3\n/\\ t = <<[x |-> 1], [x |-> 2], [x |-> 3]>>");
		expectedTrace.add("/\\ x = 4\n/\\ t = <<[x |-> 1], [x |-> 2], [x |-> 3], [x |-> 4]>>");
		expectedTrace.add("/\\ x = 5\n/\\ t = <<[x |-> 1], [x |-> 2], [x |-> 3], [x |-> 4], [x |-> 5]>>");
		expectedTrace.add("/\\ x = 6\n/\\ t = <<[x |-> 1], [x |-> 2], [x |-> 3], [x |-> 4], [x |-> 5], [x |-> 6]>>");
		expectedTrace.add("/\\ x = 7\n/\\ t = <<[x |-> 1], [x |-> 2], [x |-> 3], [x |-> 4], [x |-> 5], [x |-> 6], [x |-> 7]>>");

		final List<String> expectedActions = new ArrayList<>(7);
		expectedActions.add("<Initial predicate line 14, col 9 to line 14, col 13 of module TLCExtTrace>");
		for (int i = 1; i < 7; i++) {
			expectedActions.add("<Action line 14, col 21 to line 14, col 40 of module TLCExtTrace>");
		}
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);

	}
}
