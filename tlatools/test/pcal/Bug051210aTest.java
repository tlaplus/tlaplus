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
		
		assertCoverage("  line 115, col 14 to line 115, col 26 of module bug_05_12_10a: 1\n" + 
				"  line 116, col 14 to line 120, col 31 of module bug_05_12_10a: 1\n" + 
				"  line 121, col 11 to line 121, col 31 of module bug_05_12_10a: 1\n" + 
				"  line 122, col 11 to line 122, col 21 of module bug_05_12_10a: 1\n" + 
				"  line 123, col 21 to line 123, col 62 of module bug_05_12_10a: 0\n" + 
				"  line 128, col 11 to line 128, col 28 of module bug_05_12_10a: 1\n" + 
				"  line 129, col 11 to line 129, col 21 of module bug_05_12_10a: 1\n" + 
				"  line 130, col 21 to line 130, col 73 of module bug_05_12_10a: 0\n" + 
				"  line 134, col 25 to line 137, col 42 of module bug_05_12_10a: 0\n" + 
				"  line 138, col 25 to line 138, col 43 of module bug_05_12_10a: 0\n" + 
				"  line 139, col 22 to line 139, col 32 of module bug_05_12_10a: 0\n" + 
				"  line 140, col 22 to line 140, col 29 of module bug_05_12_10a: 0\n" + 
				"  line 141, col 22 to line 141, col 39 of module bug_05_12_10a: 1\n" + 
				"  line 142, col 22 to line 142, col 32 of module bug_05_12_10a: 1\n" + 
				"  line 143, col 32 to line 143, col 48 of module bug_05_12_10a: 0\n" + 
				"  line 144, col 21 to line 144, col 60 of module bug_05_12_10a: 0\n" + 
				"  line 147, col 12 to line 147, col 21 of module bug_05_12_10a: 0\n" + 
				"  line 148, col 12 to line 148, col 22 of module bug_05_12_10a: 0\n" + 
				"  line 149, col 22 to line 149, col 74 of module bug_05_12_10a: 0\n" + 
				"  line 153, col 25 to line 153, col 44 of module bug_05_12_10a: 0\n" + 
				"  line 154, col 25 to line 157, col 42 of module bug_05_12_10a: 0\n" + 
				"  line 158, col 22 to line 158, col 32 of module bug_05_12_10a: 0\n" + 
				"  line 159, col 22 to line 159, col 29 of module bug_05_12_10a: 0\n" + 
				"  line 163, col 33 to line 163, col 49 of module bug_05_12_10a: 1\n" + 
				"  line 164, col 33 to line 164, col 43 of module bug_05_12_10a: 1\n" + 
				"  line 167, col 33 to line 167, col 50 of module bug_05_12_10a: 0\n" + 
				"  line 168, col 33 to line 168, col 43 of module bug_05_12_10a: 0\n" + 
				"  line 169, col 32 to line 169, col 49 of module bug_05_12_10a: 0\n" + 
				"  line 170, col 21 to line 170, col 59 of module bug_05_12_10a: 0\n" + 
				"  line 173, col 12 to line 173, col 21 of module bug_05_12_10a: 0\n" + 
				"  line 174, col 12 to line 174, col 22 of module bug_05_12_10a: 0\n" + 
				"  line 175, col 22 to line 175, col 74 of module bug_05_12_10a: 0\n" + 
				"  line 179, col 25 to line 179, col 43 of module bug_05_12_10a: 1\n" + 
				"  line 180, col 25 to line 183, col 42 of module bug_05_12_10a: 1\n" + 
				"  line 184, col 22 to line 184, col 32 of module bug_05_12_10a: 1\n" + 
				"  line 185, col 22 to line 185, col 32 of module bug_05_12_10a: 1\n" + 
				"  line 186, col 32 to line 186, col 49 of module bug_05_12_10a: 0\n" + 
				"  line 187, col 21 to line 187, col 63 of module bug_05_12_10a: 0\n" + 
				"  line 190, col 13 to line 190, col 22 of module bug_05_12_10a: 1\n" + 
				"  line 191, col 13 to line 191, col 23 of module bug_05_12_10a: 1\n" + 
				"  line 192, col 23 to line 192, col 75 of module bug_05_12_10a: 0\n" + 
				"  line 196, col 25 to line 196, col 43 of module bug_05_12_10a: 0\n" + 
				"  line 197, col 25 to line 200, col 42 of module bug_05_12_10a: 0\n" + 
				"  line 201, col 22 to line 201, col 33 of module bug_05_12_10a: 0\n" + 
				"  line 202, col 22 to line 202, col 32 of module bug_05_12_10a: 0\n" + 
				"  line 203, col 32 to line 203, col 48 of module bug_05_12_10a: 0\n" + 
				"  line 204, col 21 to line 204, col 64 of module bug_05_12_10a: 0\n" + 
				"  line 207, col 12 to line 207, col 21 of module bug_05_12_10a: 0\n" + 
				"  line 208, col 12 to line 208, col 22 of module bug_05_12_10a: 0\n" + 
				"  line 209, col 22 to line 209, col 74 of module bug_05_12_10a: 0\n" + 
				"  line 212, col 11 to line 212, col 30 of module bug_05_12_10a: 1\n" + 
				"  line 213, col 11 to line 213, col 32 of module bug_05_12_10a: 1\n" + 
				"  line 214, col 11 to line 214, col 30 of module bug_05_12_10a: 1\n" + 
				"  line 215, col 11 to line 215, col 28 of module bug_05_12_10a: 1\n" + 
				"  line 216, col 11 to line 216, col 30 of module bug_05_12_10a: 1\n" + 
				"  line 217, col 21 to line 217, col 58 of module bug_05_12_10a: 0\n" + 
				"  line 224, col 11 to line 224, col 23 of module bug_05_12_10a: 1\n" + 
				"  line 225, col 11 to line 225, col 21 of module bug_05_12_10a: 1\n" + 
				"  line 226, col 21 to line 226, col 74 of module bug_05_12_10a: 0\n" + 
				"  line 232, col 22 to line 232, col 33 of module bug_05_12_10a: 0\n" + 
				"  line 233, col 32 to line 233, col 50 of module bug_05_12_10a: 0\n" + 
				"  line 234, col 22 to line 234, col 41 of module bug_05_12_10a: 1\n" + 
				"  line 235, col 22 to line 235, col 39 of module bug_05_12_10a: 1\n" + 
				"  line 236, col 22 to line 236, col 43 of module bug_05_12_10a: 1\n" + 
				"  line 237, col 22 to line 237, col 41 of module bug_05_12_10a: 1\n" + 
				"  line 238, col 21 to line 238, col 62 of module bug_05_12_10a: 0\n" + 
				"  line 241, col 12 to line 241, col 19 of module bug_05_12_10a: 0\n" + 
				"  line 242, col 12 to line 242, col 22 of module bug_05_12_10a: 0\n" + 
				"  line 243, col 22 to line 243, col 75 of module bug_05_12_10a: 0\n" + 
				"  line 248, col 11 to line 248, col 30 of module bug_05_12_10a: 0\n" + 
				"  line 249, col 11 to line 249, col 34 of module bug_05_12_10a: 0\n" + 
				"  line 250, col 11 to line 250, col 30 of module bug_05_12_10a: 0\n" + 
				"  line 251, col 21 to line 251, col 64 of module bug_05_12_10a: 0\n" + 
				"  line 256, col 11 to line 256, col 30 of module bug_05_12_10a: 0\n" + 
				"  line 257, col 11 to line 257, col 36 of module bug_05_12_10a: 0\n" + 
				"  line 258, col 11 to line 258, col 30 of module bug_05_12_10a: 0\n" + 
				"  line 259, col 21 to line 259, col 63 of module bug_05_12_10a: 0\n" + 
				"  line 264, col 11 to line 264, col 30 of module bug_05_12_10a: 1\n" + 
				"  line 265, col 11 to line 265, col 36 of module bug_05_12_10a: 1\n" + 
				"  line 266, col 11 to line 266, col 30 of module bug_05_12_10a: 1\n" + 
				"  line 267, col 21 to line 267, col 63 of module bug_05_12_10a: 0\n" + 
				"  line 272, col 12 to line 272, col 31 of module bug_05_12_10a: 0\n" + 
				"  line 273, col 12 to line 273, col 35 of module bug_05_12_10a: 0\n" + 
				"  line 274, col 12 to line 274, col 31 of module bug_05_12_10a: 0\n" + 
				"  line 275, col 22 to line 275, col 65 of module bug_05_12_10a: 0\n" + 
				"  line 280, col 14 to line 280, col 21 of module bug_05_12_10a: 1\n" + 
				"  line 281, col 14 to line 286, col 31 of module bug_05_12_10a: 1\n" + 
				"  line 287, col 11 to line 287, col 22 of module bug_05_12_10a: 1\n" + 
				"  line 288, col 11 to line 288, col 17 of module bug_05_12_10a: 1\n" + 
				"  line 289, col 11 to line 289, col 21 of module bug_05_12_10a: 1\n" + 
				"  line 290, col 21 to line 290, col 58 of module bug_05_12_10a: 0\n" + 
				"  line 294, col 11 to line 294, col 22 of module bug_05_12_10a: 1\n" + 
				"  line 295, col 21 to line 295, col 77 of module bug_05_12_10a: 0\n" + 
				"  line 300, col 41 to line 300, col 44 of module bug_05_12_10a: 0");
	}
}
