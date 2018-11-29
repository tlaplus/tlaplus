/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
package pcal;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

public class TestTest extends PCalModelCheckerTestCase {

	public TestTest() {
		super("Test", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "4"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "5", "4", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "4"));

		assertUncovered("line 47, col 31 to line 47, col 37 of module Test: 0\n"
				+ "line 48, col 31 to line 48, col 37 of module Test: 0\n"
				+ "line 51, col 24 to line 51, col 30 of module Test: 0\n"
				+ "line 52, col 9 to line 52, col 28 of module Test: 0\n"
				+ "line 53, col 9 to line 53, col 28 of module Test: 0\n"
				+ "line 54, col 9 to line 54, col 14 of module Test: 0\n"
				+ "line 68, col 43 to line 68, col 49 of module Test: 0\n"
				+ "line 69, col 43 to line 69, col 49 of module Test: 0\n"
				+ "line 72, col 36 to line 72, col 42 of module Test: 0\n"
				+ "line 73, col 21 to line 73, col 26 of module Test: 0\n"
				+ "line 84, col 32 to line 84, col 38 of module Test: 0\n"
				+ "line 87, col 25 to line 87, col 31 of module Test: 0");
	}
}
