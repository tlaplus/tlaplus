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

public class FastMutex2Test extends PCalModelCheckerTestCase {

	public FastMutex2Test() {
		super("FastMutex2", "pcal", new String[] {"-wf"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "1415"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2679", "1415", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "60"));

		assertCoverage("  line 101, col 19 to line 101, col 50 of module FastMutex2: 119\n" + 
				"  line 102, col 29 to line 102, col 65 of module FastMutex2: 0\n" + 
				"  line 105, col 16 to line 105, col 45 of module FastMutex2: 119\n" + 
				"  line 106, col 16 to line 106, col 47 of module FastMutex2: 119\n" + 
				"  line 107, col 26 to line 107, col 59 of module FastMutex2: 0\n" + 
				"  line 110, col 16 to line 110, col 24 of module FastMutex2: 119\n" + 
				"  line 111, col 16 to line 111, col 47 of module FastMutex2: 119\n" + 
				"  line 112, col 26 to line 112, col 59 of module FastMutex2: 0\n" + 
				"  line 116, col 27 to line 116, col 58 of module FastMutex2: 40\n" + 
				"  line 117, col 27 to line 117, col 58 of module FastMutex2: 76\n" + 
				"  line 118, col 26 to line 118, col 62 of module FastMutex2: 0\n" + 
				"  line 121, col 16 to line 121, col 46 of module FastMutex2: 82\n" + 
				"  line 122, col 16 to line 122, col 47 of module FastMutex2: 82\n" + 
				"  line 123, col 26 to line 123, col 59 of module FastMutex2: 0\n" + 
				"  line 128, col 16 to line 128, col 50 of module FastMutex2: 42\n" + 
				"  line 129, col 26 to line 129, col 62 of module FastMutex2: 0\n" + 
				"  line 132, col 16 to line 132, col 24 of module FastMutex2: 98\n" + 
				"  line 133, col 16 to line 133, col 47 of module FastMutex2: 98\n" + 
				"  line 134, col 26 to line 134, col 59 of module FastMutex2: 0\n" + 
				"  line 138, col 27 to line 138, col 58 of module FastMutex2: 80\n" + 
				"  line 139, col 27 to line 139, col 58 of module FastMutex2: 62\n" + 
				"  line 140, col 26 to line 140, col 62 of module FastMutex2: 0\n" + 
				"  line 143, col 16 to line 143, col 46 of module FastMutex2: 80\n" + 
				"  line 144, col 16 to line 144, col 42 of module FastMutex2: 80\n" + 
				"  line 145, col 16 to line 145, col 47 of module FastMutex2: 80\n" + 
				"  line 146, col 26 to line 146, col 56 of module FastMutex2: 0\n" + 
				"  line 151, col 27 to line 151, col 61 of module FastMutex2: 50\n" + 
				"  line 152, col 27 to line 152, col 58 of module FastMutex2: 50\n" + 
				"  line 153, col 27 to line 153, col 59 of module FastMutex2: 30\n" + 
				"  line 154, col 27 to line 154, col 32 of module FastMutex2: 30\n" + 
				"  line 155, col 26 to line 155, col 59 of module FastMutex2: 0\n" + 
				"  line 160, col 28 to line 160, col 67 of module FastMutex2: 12\n" + 
				"  line 162, col 38 to line 162, col 43 of module FastMutex2: 12\n" + 
				"  line 163, col 17 to line 163, col 48 of module FastMutex2: 24\n" + 
				"  line 164, col 27 to line 164, col 55 of module FastMutex2: 0\n" + 
				"  line 169, col 27 to line 169, col 59 of module FastMutex2: 86\n" + 
				"  line 170, col 37 to line 170, col 42 of module FastMutex2: 86\n" + 
				"  line 171, col 27 to line 171, col 67 of module FastMutex2: 18\n" + 
				"  line 172, col 27 to line 172, col 61 of module FastMutex2: 18\n" + 
				"  line 173, col 26 to line 173, col 54 of module FastMutex2: 0\n" + 
				"  line 176, col 17 to line 176, col 22 of module FastMutex2: 86\n" + 
				"  line 177, col 17 to line 177, col 49 of module FastMutex2: 86\n" + 
				"  line 178, col 27 to line 178, col 60 of module FastMutex2: 0\n" + 
				"  line 181, col 17 to line 181, col 47 of module FastMutex2: 128\n" + 
				"  line 182, col 17 to line 182, col 51 of module FastMutex2: 128\n" + 
				"  line 183, col 27 to line 183, col 60 of module FastMutex2: 0\n" + 
				"  line 191, col 20 to line 191, col 52 of module FastMutex2: 119\n" + 
				"  line 192, col 30 to line 192, col 66 of module FastMutex2: 0\n" + 
				"  line 195, col 17 to line 195, col 46 of module FastMutex2: 119\n" + 
				"  line 196, col 17 to line 196, col 49 of module FastMutex2: 119\n" + 
				"  line 197, col 27 to line 197, col 60 of module FastMutex2: 0\n" + 
				"  line 200, col 17 to line 200, col 25 of module FastMutex2: 119\n" + 
				"  line 201, col 17 to line 201, col 49 of module FastMutex2: 119\n" + 
				"  line 202, col 27 to line 202, col 60 of module FastMutex2: 0\n" + 
				"  line 206, col 28 to line 206, col 60 of module FastMutex2: 40\n" + 
				"  line 207, col 28 to line 207, col 60 of module FastMutex2: 76\n" + 
				"  line 208, col 27 to line 208, col 63 of module FastMutex2: 0\n" + 
				"  line 211, col 17 to line 211, col 47 of module FastMutex2: 82\n" + 
				"  line 212, col 17 to line 212, col 49 of module FastMutex2: 82\n" + 
				"  line 213, col 27 to line 213, col 60 of module FastMutex2: 0\n" + 
				"  line 218, col 17 to line 218, col 52 of module FastMutex2: 42\n" + 
				"  line 219, col 27 to line 219, col 63 of module FastMutex2: 0\n" + 
				"  line 222, col 17 to line 222, col 25 of module FastMutex2: 100\n" + 
				"  line 223, col 17 to line 223, col 49 of module FastMutex2: 100\n" + 
				"  line 224, col 27 to line 224, col 60 of module FastMutex2: 0\n" + 
				"  line 228, col 28 to line 228, col 60 of module FastMutex2: 80\n" + 
				"  line 229, col 28 to line 229, col 60 of module FastMutex2: 64\n" + 
				"  line 230, col 27 to line 230, col 63 of module FastMutex2: 0\n" + 
				"  line 233, col 17 to line 233, col 47 of module FastMutex2: 80\n" + 
				"  line 234, col 17 to line 234, col 45 of module FastMutex2: 80\n" + 
				"  line 235, col 17 to line 235, col 49 of module FastMutex2: 80\n" + 
				"  line 236, col 27 to line 236, col 56 of module FastMutex2: 0\n" + 
				"  line 241, col 28 to line 241, col 65 of module FastMutex2: 40\n" + 
				"  line 242, col 28 to line 242, col 60 of module FastMutex2: 40\n" + 
				"  line 243, col 28 to line 243, col 61 of module FastMutex2: 30\n" + 
				"  line 244, col 28 to line 244, col 35 of module FastMutex2: 30\n" + 
				"  line 245, col 27 to line 245, col 59 of module FastMutex2: 0\n" + 
				"  line 250, col 29 to line 250, col 70 of module FastMutex2: 12\n" + 
				"  line 252, col 39 to line 252, col 45 of module FastMutex2: 12\n" + 
				"  line 253, col 18 to line 253, col 50 of module FastMutex2: 24\n" + 
				"  line 254, col 28 to line 254, col 55 of module FastMutex2: 0\n" + 
				"  line 259, col 28 to line 259, col 61 of module FastMutex2: 88\n" + 
				"  line 260, col 38 to line 260, col 44 of module FastMutex2: 88\n" + 
				"  line 261, col 28 to line 261, col 70 of module FastMutex2: 18\n" + 
				"  line 262, col 28 to line 262, col 63 of module FastMutex2: 18\n" + 
				"  line 263, col 27 to line 263, col 54 of module FastMutex2: 0\n" + 
				"  line 266, col 18 to line 266, col 23 of module FastMutex2: 88\n" + 
				"  line 267, col 18 to line 267, col 51 of module FastMutex2: 88\n" + 
				"  line 268, col 28 to line 268, col 61 of module FastMutex2: 0\n" + 
				"  line 271, col 18 to line 271, col 48 of module FastMutex2: 130\n" + 
				"  line 272, col 18 to line 272, col 53 of module FastMutex2: 130\n" + 
				"  line 273, col 28 to line 273, col 61 of module FastMutex2: 0");
	}
}
