/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
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

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class ViewMapTest extends ModelCheckerTestCase {

	public ViewMapTest() {
		super("ViewMap", new String[] { "-view" }, ExitStatus.VIOLATION_SAFETY);
	}


	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertFalse(recorder.recorded(EC.TLC_BUG));

		assertTrue(recorder.recorded(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT));
		
		final List<String> expectedTrace = new ArrayList<String>(8);
		expectedTrace.add("/\\ buffer = <<>>\n/\\ waitset = {}");
		expectedTrace.add("/\\ buffer = <<>>\n/\\ waitset = {c1}");
		expectedTrace.add("/\\ buffer = <<>>\n/\\ waitset = {c1, c2}");
		expectedTrace.add("/\\ buffer = <<\"d\">>\n/\\ waitset = {c2}");

		expectedTrace.add("/\\ buffer = <<\"d\">>\n/\\ waitset = {c2, p1}");
		expectedTrace.add("/\\ buffer = << >>\n/\\ waitset = {p1}");
		expectedTrace.add("/\\ buffer = << >>\n/\\ waitset = {c1, p1}");
		expectedTrace.add("/\\ buffer = << >>\n/\\ waitset = {c1, c2, p1}");
		final List<String> expectedActions = new ArrayList<>();
		expectedActions.add(isExtendedTLCState()
				? "<Init line 53, col 9 to line 56, col 63 of module ViewMap>"
				: TLCStateInfo.INITIAL_PREDICATE);
		expectedActions.add("<lbc line 73, col 14 to line 84, col 60 of module ViewMap>");
		expectedActions.add("<lbc line 73, col 14 to line 84, col 60 of module ViewMap>");
		expectedActions.add("<lbp line 58, col 14 to line 69, col 60 of module ViewMap>");
		expectedActions.add("<lbp line 58, col 14 to line 69, col 60 of module ViewMap>");
		expectedActions.add("<lbc line 73, col 14 to line 84, col 60 of module ViewMap>");
		expectedActions.add("<lbc line 73, col 14 to line 84, col 60 of module ViewMap>");
		expectedActions.add("<lbc line 73, col 14 to line 84, col 60 of module ViewMap>");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);

		assertUncovered("line 91, col 60 to line 91, col 73 of module ViewMap: 0");
	}
}
