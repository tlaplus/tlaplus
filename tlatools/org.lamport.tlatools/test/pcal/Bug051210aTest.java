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

public class Bug051210aTest extends PCalModelCheckerTestCase {

	public Bug051210aTest() {
		super("bug_05_12_10a", "pcal");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "15", "14", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "14"));
		
		assertUncovered("  line 134, col 25 to line 137, col 42 of module bug_05_12_10a: 0\n" + 
				"  line 138, col 25 to line 138, col 43 of module bug_05_12_10a: 0\n" + 
				"  line 139, col 22 to line 139, col 32 of module bug_05_12_10a: 0\n" + 
				"  line 140, col 22 to line 140, col 29 of module bug_05_12_10a: 0\n" + 
				"  line 147, col 12 to line 147, col 21 of module bug_05_12_10a: 0\n" + 
				"  line 148, col 12 to line 148, col 22 of module bug_05_12_10a: 0\n" + 
				"  line 149, col 12 to line 149, col 74 of module bug_05_12_10a: 0\n" + 
				"  line 153, col 25 to line 153, col 44 of module bug_05_12_10a: 0\n" + 
				"  line 154, col 25 to line 157, col 42 of module bug_05_12_10a: 0\n" + 
				"  line 158, col 22 to line 158, col 32 of module bug_05_12_10a: 0\n" + 
				"  line 159, col 22 to line 159, col 29 of module bug_05_12_10a: 0\n" + 
				"  line 167, col 33 to line 167, col 50 of module bug_05_12_10a: 0\n" + 
				"  line 168, col 33 to line 168, col 43 of module bug_05_12_10a: 0\n" + 
				"  line 173, col 12 to line 173, col 21 of module bug_05_12_10a: 0\n" + 
				"  line 174, col 12 to line 174, col 22 of module bug_05_12_10a: 0\n" + 
				"  line 175, col 12 to line 175, col 74 of module bug_05_12_10a: 0\n" + 
				"  line 196, col 25 to line 196, col 43 of module bug_05_12_10a: 0\n" + 
				"  line 197, col 25 to line 200, col 42 of module bug_05_12_10a: 0\n" + 
				"  line 201, col 22 to line 201, col 33 of module bug_05_12_10a: 0\n" + 
				"  line 202, col 22 to line 202, col 32 of module bug_05_12_10a: 0\n" + 
				"  line 203, col 22 to line 203, col 48 of module bug_05_12_10a: 0\n" + 
				"  line 204, col 11 to line 204, col 64 of module bug_05_12_10a: 0\n" + 
				"  line 207, col 12 to line 207, col 21 of module bug_05_12_10a: 0\n" + 
				"  line 208, col 12 to line 208, col 22 of module bug_05_12_10a: 0\n" + 
				"  line 209, col 12 to line 209, col 74 of module bug_05_12_10a: 0\n" + 
				"  line 232, col 22 to line 232, col 33 of module bug_05_12_10a: 0\n" + 
				"  line 233, col 22 to line 233, col 50 of module bug_05_12_10a: 0\n" + 
				"  line 241, col 12 to line 241, col 19 of module bug_05_12_10a: 0\n" + 
				"  line 242, col 12 to line 242, col 22 of module bug_05_12_10a: 0\n" + 
				"  line 243, col 12 to line 243, col 75 of module bug_05_12_10a: 0\n" + 
				"  line 248, col 11 to line 248, col 30 of module bug_05_12_10a: 0\n" + 
				"  line 249, col 11 to line 249, col 34 of module bug_05_12_10a: 0\n" + 
				"  line 250, col 11 to line 250, col 30 of module bug_05_12_10a: 0\n" + 
				"  line 251, col 11 to line 251, col 64 of module bug_05_12_10a: 0\n" + 
				"  line 256, col 11 to line 256, col 30 of module bug_05_12_10a: 0\n" + 
				"  line 257, col 11 to line 257, col 36 of module bug_05_12_10a: 0\n" + 
				"  line 258, col 11 to line 258, col 30 of module bug_05_12_10a: 0\n" + 
				"  line 259, col 11 to line 259, col 63 of module bug_05_12_10a: 0\n" + 
				"  line 272, col 12 to line 272, col 31 of module bug_05_12_10a: 0\n" + 
				"  line 273, col 12 to line 273, col 35 of module bug_05_12_10a: 0\n" + 
				"  line 274, col 12 to line 274, col 31 of module bug_05_12_10a: 0\n" + 
				"  line 275, col 12 to line 275, col 65 of module bug_05_12_10a: 0");
	}
}
