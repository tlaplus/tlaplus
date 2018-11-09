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

public class Bug060125Test extends PCalModelCheckerTestCase {

	public Bug060125Test() {
		super("bug_06_01_25", "pcal");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "130", "64", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "15"));
		
		assertCoverage("  line 121, col 17 to line 121, col 43 of module bug_06_01_25: 16\n" + 
				"  line 122, col 17 to line 122, col 43 of module bug_06_01_25: 16\n" + 
				"  line 123, col 17 to line 123, col 43 of module bug_06_01_25: 16\n" + 
				"  line 124, col 17 to line 124, col 64 of module bug_06_01_25: 16\n" + 
				"  line 125, col 17 to line 125, col 61 of module bug_06_01_25: 16\n" + 
				"  line 126, col 17 to line 126, col 67 of module bug_06_01_25: 16\n" + 
				"  line 127, col 17 to line 127, col 22 of module bug_06_01_25: 16\n" + 
				"  line 135, col 27 to line 135, col 53 of module bug_06_01_25: 16\n" + 
				"  line 136, col 27 to line 136, col 53 of module bug_06_01_25: 16\n" + 
				"  line 137, col 27 to line 137, col 53 of module bug_06_01_25: 16\n" + 
				"  line 138, col 27 to line 138, col 53 of module bug_06_01_25: 0\n" + 
				"  line 139, col 27 to line 139, col 53 of module bug_06_01_25: 0\n" + 
				"  line 140, col 27 to line 140, col 53 of module bug_06_01_25: 0\n" + 
				"  line 141, col 16 to line 141, col 48 of module bug_06_01_25: 16\n" + 
				"  line 142, col 26 to line 142, col 42 of module bug_06_01_25: 0\n" + 
				"  line 151, col 24 to line 151, col 50 of module bug_06_01_25: 32\n" + 
				"  line 152, col 24 to line 152, col 50 of module bug_06_01_25: 32\n" + 
				"  line 153, col 24 to line 153, col 50 of module bug_06_01_25: 32\n" + 
				"  line 154, col 17 to line 154, col 48 of module bug_06_01_25: 32\n" + 
				"  line 155, col 27 to line 155, col 43 of module bug_06_01_25: 0\n" + 
				"  line 162, col 27 to line 162, col 53 of module bug_06_01_25: 0\n" + 
				"  line 163, col 27 to line 163, col 53 of module bug_06_01_25: 0\n" + 
				"  line 164, col 27 to line 164, col 53 of module bug_06_01_25: 0\n" + 
				"  line 165, col 27 to line 167, col 75 of module bug_06_01_25: 0\n" + 
				"  line 168, col 27 to line 168, col 58 of module bug_06_01_25: 0\n" + 
				"  line 169, col 27 to line 169, col 58 of module bug_06_01_25: 16\n" + 
				"  line 170, col 37 to line 170, col 52 of module bug_06_01_25: 0\n" + 
				"  line 171, col 26 to line 171, col 39 of module bug_06_01_25: 0\n" + 
				"  line 174, col 19 to line 176, col 67 of module bug_06_01_25: 16\n" + 
				"  line 177, col 19 to line 180, col 67 of module bug_06_01_25: 16\n" + 
				"  line 181, col 16 to line 181, col 48 of module bug_06_01_25: 16\n" + 
				"  line 182, col 26 to line 182, col 41 of module bug_06_01_25: 0\n" + 
				"  line 192, col 16 to line 192, col 47 of module bug_06_01_25: 16\n" + 
				"  line 193, col 26 to line 193, col 51 of module bug_06_01_25: 0\n" + 
				"  line 196, col 16 to line 196, col 42 of module bug_06_01_25: 16\n" + 
				"  line 197, col 16 to line 197, col 42 of module bug_06_01_25: 16\n" + 
				"  line 198, col 16 to line 198, col 42 of module bug_06_01_25: 16\n" + 
				"  line 207, col 16 to line 207, col 49 of module bug_06_01_25: 16\n" + 
				"  line 208, col 26 to line 208, col 42 of module bug_06_01_25: 0\n" + 
				"  line 218, col 70 to line 218, col 73 of module bug_06_01_25: 0");
	}
}
