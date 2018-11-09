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

public class TestReplaceTest extends PCalModelCheckerTestCase {

	public TestReplaceTest() {
		super("TestReplace", "pcal");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "18", "17", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "17"));

	assertCoverage("  line 100, col 10 to line 100, col 29 of module TestReplace: 2\n" +
		"  line 101, col 10 to line 101, col 29 of module TestReplace: 2\n" +
		"  line 102, col 20 to line 102, col 52 of module TestReplace: 0\n" +
		"  line 108, col 11 to line 108, col 20 of module TestReplace: 1\n" +
		"  line 109, col 21 to line 109, col 68 of module TestReplace: 0\n" +
		"  line 113, col 21 to line 113, col 30 of module TestReplace: 1\n" +
		"  line 114, col 21 to line 114, col 30 of module TestReplace: 1\n" +
		"  line 121, col 32 to line 121, col 41 of module TestReplace: 1\n" +
		"  line 124, col 32 to line 124, col 41 of module TestReplace: 0\n" +
		"  line 125, col 21 to line 125, col 26 of module TestReplace: 1\n" +
		"  line 126, col 20 to line 126, col 64 of module TestReplace: 0\n" +
		"  line 129, col 13 to line 133, col 30 of module TestReplace: 1\n" +
		"  line 134, col 13 to line 134, col 20 of module TestReplace: 1\n" +
		"  line 135, col 13 to line 135, col 19 of module TestReplace: 1\n" +
		"  line 136, col 10 to line 136, col 19 of module TestReplace: 1\n" +
		"  line 137, col 20 to line 137, col 52 of module TestReplace: 0\n" +
		"  line 141, col 10 to line 141, col 26 of module TestReplace: 1\n" +
		"  line 143, col 10 to line 143, col 19 of module TestReplace: 1\n" +
		"  line 144, col 20 to line 144, col 63 of module TestReplace: 0\n" +
		"  line 147, col 10 to line 147, col 29 of module TestReplace: 1\n" +
		"  line 148, col 10 to line 148, col 29 of module TestReplace: 1\n" +
		"  line 149, col 10 to line 149, col 27 of module TestReplace: 1\n" +
		"  line 150, col 10 to line 150, col 31 of module TestReplace: 1\n" +
		"  line 151, col 10 to line 151, col 31 of module TestReplace: 1\n" +
		"  line 152, col 10 to line 152, col 29 of module TestReplace: 1\n" +
		"  line 153, col 20 to line 153, col 43 of module TestReplace: 0\n" +
		"  line 159, col 9 to line 159, col 19 of module TestReplace: 1\n" +
		"  line 160, col 19 to line 160, col 66 of module TestReplace: 0\n" +
		"  line 164, col 22 to line 164, col 31 of module TestReplace: 1\n" +
		"  line 165, col 22 to line 165, col 32 of module TestReplace: 1\n" +
		"  line 172, col 33 to line 172, col 41 of module TestReplace: 1\n" +
		"  line 175, col 33 to line 175, col 41 of module TestReplace: 0\n" +
		"  line 176, col 22 to line 176, col 27 of module TestReplace: 1\n" +
		"  line 177, col 21 to line 177, col 65 of module TestReplace: 0\n" +
		"  line 180, col 12 to line 184, col 29 of module TestReplace: 1\n" +
		"  line 185, col 12 to line 185, col 18 of module TestReplace: 1\n" +
		"  line 186, col 12 to line 186, col 18 of module TestReplace: 1\n" +
		"  line 187, col 9 to line 187, col 18 of module TestReplace: 1\n" +
		"  line 188, col 19 to line 188, col 51 of module TestReplace: 0\n" +
		"  line 192, col 9 to line 192, col 22 of module TestReplace: 1\n" +
		"  line 194, col 9 to line 194, col 17 of module TestReplace: 1\n" +
		"  line 195, col 19 to line 195, col 63 of module TestReplace: 0\n" +
		"  line 198, col 9 to line 198, col 28 of module TestReplace: 1\n" +
		"  line 199, col 9 to line 199, col 26 of module TestReplace: 1\n" +
		"  line 200, col 9 to line 200, col 26 of module TestReplace: 1\n" +
		"  line 201, col 9 to line 201, col 26 of module TestReplace: 1\n" +
		"  line 202, col 9 to line 202, col 26 of module TestReplace: 1\n" +
		"  line 203, col 9 to line 203, col 28 of module TestReplace: 1\n" +
		"  line 204, col 19 to line 204, col 47 of module TestReplace: 0\n" +
		"  line 209, col 16 to line 215, col 33 of module TestReplace: 1\n" +
		"  line 216, col 16 to line 216, col 23 of module TestReplace: 1\n" +
		"  line 217, col 16 to line 217, col 23 of module TestReplace: 1\n" +
		"  line 218, col 13 to line 218, col 19 of module TestReplace: 1\n" +
		"  line 219, col 13 to line 219, col 20 of module TestReplace: 1\n" +
		"  line 220, col 13 to line 220, col 23 of module TestReplace: 1\n" +
		"  line 221, col 23 to line 221, col 46 of module TestReplace: 0\n" +
		"  line 224, col 12 to line 230, col 29 of module TestReplace: 1\n" +
		"  line 231, col 12 to line 231, col 17 of module TestReplace: 1\n" +
		"  line 232, col 12 to line 232, col 17 of module TestReplace: 1\n" +
		"  line 233, col 9 to line 233, col 14 of module TestReplace: 1\n" +
		"  line 234, col 9 to line 234, col 15 of module TestReplace: 1\n" +
		"  line 235, col 9 to line 235, col 17 of module TestReplace: 1\n" +
		"  line 236, col 19 to line 236, col 47 of module TestReplace: 0\n" +
		"  line 240, col 41 to line 240, col 44 of module TestReplace: 0\n" +
		"  line 98, col 10 to line 98, col 29 of module TestReplace: 2\n" +
		"  line 99, col 10 to line 99, col 29 of module TestReplace: 2");
	}
}
