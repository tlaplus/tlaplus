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
import tlc2.tool.liveness.ModelCheckerTestCase;

public class ViewMapTest extends ModelCheckerTestCase {

	public ViewMapTest() {
		super("ViewMap", new String[] { "-view" });
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
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

	assertCoverage("  line 60, col 28 to line 60, col 59 of module ViewMap: 6\n" +
		"  line 61, col 28 to line 61, col 60 of module ViewMap: 6\n" +
		"  line 62, col 38 to line 62, col 43 of module ViewMap: 6\n" +
		"  line 63, col 28 to line 63, col 56 of module ViewMap: 8\n" +
		"  line 66, col 41 to line 66, col 64 of module ViewMap: 7\n" +
		"  line 68, col 49 to line 68, col 55 of module ViewMap: 1\n" +
		"  line 69, col 28 to line 69, col 60 of module ViewMap: 8\n" +
		"  line 75, col 28 to line 75, col 59 of module ViewMap: 12\n" +
		"  line 76, col 28 to line 76, col 60 of module ViewMap: 12\n" +
		"  line 77, col 38 to line 77, col 43 of module ViewMap: 12\n" +
		"  line 78, col 28 to line 78, col 55 of module ViewMap: 16\n" +
		"  line 81, col 41 to line 81, col 64 of module ViewMap: 14\n" +
		"  line 83, col 49 to line 83, col 55 of module ViewMap: 2\n" +
		"  line 84, col 28 to line 84, col 60 of module ViewMap: 16\n" +
		"  line 91, col 70 to line 91, col 73 of module ViewMap: 0");
	}
}
