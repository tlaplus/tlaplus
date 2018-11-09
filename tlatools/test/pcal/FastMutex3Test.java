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

public class FastMutex3Test extends PCalModelCheckerTestCase {

	public FastMutex3Test() {
		super("FastMutex3", "pcal", new String[] {"-wf"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "1415"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2679", "1415", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "60"));

		assertCoverage("  line 101, col 13 to line 101, col 41 of module FastMutex3: 119\n" + 
				"  line 102, col 23 to line 102, col 59 of module FastMutex3: 0\n" + 
				"  line 105, col 10 to line 105, col 36 of module FastMutex3: 119\n" + 
				"  line 106, col 10 to line 106, col 38 of module FastMutex3: 119\n" + 
				"  line 107, col 20 to line 107, col 53 of module FastMutex3: 0\n" + 
				"  line 110, col 10 to line 110, col 15 of module FastMutex3: 119\n" + 
				"  line 111, col 10 to line 111, col 38 of module FastMutex3: 119\n" + 
				"  line 112, col 20 to line 112, col 53 of module FastMutex3: 0\n" + 
				"  line 116, col 21 to line 116, col 49 of module FastMutex3: 40\n" + 
				"  line 117, col 21 to line 117, col 49 of module FastMutex3: 76\n" + 
				"  line 118, col 20 to line 118, col 56 of module FastMutex3: 0\n" + 
				"  line 121, col 10 to line 121, col 37 of module FastMutex3: 82\n" + 
				"  line 122, col 10 to line 122, col 38 of module FastMutex3: 82\n" + 
				"  line 123, col 20 to line 123, col 53 of module FastMutex3: 0\n" + 
				"  line 128, col 10 to line 128, col 41 of module FastMutex3: 42\n" + 
				"  line 129, col 20 to line 129, col 56 of module FastMutex3: 0\n" + 
				"  line 132, col 10 to line 132, col 15 of module FastMutex3: 98\n" + 
				"  line 133, col 10 to line 133, col 38 of module FastMutex3: 98\n" + 
				"  line 134, col 20 to line 134, col 53 of module FastMutex3: 0\n" + 
				"  line 138, col 21 to line 138, col 49 of module FastMutex3: 80\n" + 
				"  line 139, col 21 to line 139, col 49 of module FastMutex3: 62\n" + 
				"  line 140, col 20 to line 140, col 56 of module FastMutex3: 0\n" + 
				"  line 143, col 10 to line 143, col 37 of module FastMutex3: 80\n" + 
				"  line 144, col 10 to line 144, col 15 of module FastMutex3: 80\n" + 
				"  line 145, col 10 to line 145, col 38 of module FastMutex3: 80\n" + 
				"  line 146, col 20 to line 146, col 50 of module FastMutex3: 0\n" + 
				"  line 151, col 21 to line 151, col 28 of module FastMutex3: 50\n" + 
				"  line 152, col 21 to line 152, col 49 of module FastMutex3: 50\n" + 
				"  line 153, col 21 to line 153, col 50 of module FastMutex3: 30\n" + 
				"  line 154, col 21 to line 154, col 26 of module FastMutex3: 30\n" + 
				"  line 155, col 20 to line 155, col 53 of module FastMutex3: 0\n" + 
				"  line 160, col 22 to line 160, col 35 of module FastMutex3: 12\n" + 
				"  line 162, col 32 to line 162, col 37 of module FastMutex3: 12\n" + 
				"  line 163, col 11 to line 163, col 39 of module FastMutex3: 24\n" + 
				"  line 164, col 21 to line 164, col 49 of module FastMutex3: 0\n" + 
				"  line 169, col 21 to line 169, col 50 of module FastMutex3: 86\n" + 
				"  line 170, col 31 to line 170, col 36 of module FastMutex3: 86\n" + 
				"  line 171, col 21 to line 171, col 35 of module FastMutex3: 18\n" + 
				"  line 172, col 21 to line 172, col 52 of module FastMutex3: 18\n" + 
				"  line 173, col 20 to line 173, col 48 of module FastMutex3: 0\n" + 
				"  line 176, col 11 to line 176, col 16 of module FastMutex3: 86\n" + 
				"  line 177, col 11 to line 177, col 40 of module FastMutex3: 86\n" + 
				"  line 178, col 21 to line 178, col 54 of module FastMutex3: 0\n" + 
				"  line 181, col 11 to line 181, col 38 of module FastMutex3: 128\n" + 
				"  line 182, col 11 to line 182, col 42 of module FastMutex3: 128\n" + 
				"  line 183, col 21 to line 183, col 54 of module FastMutex3: 0\n" + 
				"  line 189, col 20 to line 189, col 52 of module FastMutex3: 119\n" + 
				"  line 190, col 30 to line 190, col 66 of module FastMutex3: 0\n" + 
				"  line 193, col 17 to line 193, col 46 of module FastMutex3: 119\n" + 
				"  line 194, col 17 to line 194, col 49 of module FastMutex3: 119\n" + 
				"  line 195, col 27 to line 195, col 60 of module FastMutex3: 0\n" + 
				"  line 198, col 17 to line 198, col 25 of module FastMutex3: 119\n" + 
				"  line 199, col 17 to line 199, col 49 of module FastMutex3: 119\n" + 
				"  line 200, col 27 to line 200, col 60 of module FastMutex3: 0\n" + 
				"  line 204, col 28 to line 204, col 60 of module FastMutex3: 40\n" + 
				"  line 205, col 28 to line 205, col 60 of module FastMutex3: 76\n" + 
				"  line 206, col 27 to line 206, col 63 of module FastMutex3: 0\n" + 
				"  line 209, col 17 to line 209, col 47 of module FastMutex3: 82\n" + 
				"  line 210, col 17 to line 210, col 49 of module FastMutex3: 82\n" + 
				"  line 211, col 27 to line 211, col 60 of module FastMutex3: 0\n" + 
				"  line 216, col 17 to line 216, col 52 of module FastMutex3: 42\n" + 
				"  line 217, col 27 to line 217, col 63 of module FastMutex3: 0\n" + 
				"  line 220, col 17 to line 220, col 25 of module FastMutex3: 100\n" + 
				"  line 221, col 17 to line 221, col 49 of module FastMutex3: 100\n" + 
				"  line 222, col 27 to line 222, col 60 of module FastMutex3: 0\n" + 
				"  line 226, col 28 to line 226, col 60 of module FastMutex3: 80\n" + 
				"  line 227, col 28 to line 227, col 60 of module FastMutex3: 64\n" + 
				"  line 228, col 27 to line 228, col 63 of module FastMutex3: 0\n" + 
				"  line 231, col 17 to line 231, col 47 of module FastMutex3: 80\n" + 
				"  line 232, col 17 to line 232, col 45 of module FastMutex3: 80\n" + 
				"  line 233, col 17 to line 233, col 49 of module FastMutex3: 80\n" + 
				"  line 234, col 27 to line 234, col 56 of module FastMutex3: 0\n" + 
				"  line 239, col 28 to line 239, col 65 of module FastMutex3: 40\n" + 
				"  line 240, col 28 to line 240, col 60 of module FastMutex3: 40\n" + 
				"  line 241, col 28 to line 241, col 61 of module FastMutex3: 30\n" + 
				"  line 242, col 28 to line 242, col 35 of module FastMutex3: 30\n" + 
				"  line 243, col 27 to line 243, col 59 of module FastMutex3: 0\n" + 
				"  line 248, col 29 to line 248, col 70 of module FastMutex3: 12\n" + 
				"  line 250, col 39 to line 250, col 45 of module FastMutex3: 12\n" + 
				"  line 251, col 18 to line 251, col 50 of module FastMutex3: 24\n" + 
				"  line 252, col 28 to line 252, col 55 of module FastMutex3: 0\n" + 
				"  line 257, col 28 to line 257, col 61 of module FastMutex3: 88\n" + 
				"  line 258, col 38 to line 258, col 44 of module FastMutex3: 88\n" + 
				"  line 259, col 28 to line 259, col 70 of module FastMutex3: 18\n" + 
				"  line 260, col 28 to line 260, col 63 of module FastMutex3: 18\n" + 
				"  line 261, col 27 to line 261, col 54 of module FastMutex3: 0\n" + 
				"  line 264, col 18 to line 264, col 23 of module FastMutex3: 88\n" + 
				"  line 265, col 18 to line 265, col 51 of module FastMutex3: 88\n" + 
				"  line 266, col 28 to line 266, col 61 of module FastMutex3: 0\n" + 
				"  line 269, col 18 to line 269, col 48 of module FastMutex3: 130\n" + 
				"  line 270, col 18 to line 270, col 53 of module FastMutex3: 130\n" + 
				"  line 271, col 28 to line 271, col 61 of module FastMutex3: 0");
	}
}
