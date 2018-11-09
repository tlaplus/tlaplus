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

public class FastMutexWithGotoTest extends PCalModelCheckerTestCase {

	public FastMutexWithGotoTest() {
		super("FastMutexWithGoto", "pcal");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "1415"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2679", "1415", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "58"));

		assertCoverage("  line 100, col 27 to line 100, col 58 of module FastMutexWithGoto: 160\n" + 
				"  line 101, col 27 to line 101, col 58 of module FastMutexWithGoto: 126\n" + 
				"  line 102, col 26 to line 102, col 41 of module FastMutexWithGoto: 0\n" + 
				"  line 105, col 16 to line 105, col 46 of module FastMutexWithGoto: 160\n" + 
				"  line 106, col 16 to line 106, col 42 of module FastMutexWithGoto: 160\n" + 
				"  line 107, col 16 to line 107, col 47 of module FastMutexWithGoto: 160\n" + 
				"  line 108, col 26 to line 108, col 35 of module FastMutexWithGoto: 0\n" + 
				"  line 113, col 27 to line 113, col 61 of module FastMutexWithGoto: 90\n" + 
				"  line 114, col 27 to line 114, col 58 of module FastMutexWithGoto: 90\n" + 
				"  line 115, col 27 to line 115, col 58 of module FastMutexWithGoto: 60\n" + 
				"  line 116, col 27 to line 116, col 32 of module FastMutexWithGoto: 60\n" + 
				"  line 117, col 26 to line 117, col 38 of module FastMutexWithGoto: 0\n" + 
				"  line 121, col 27 to line 121, col 59 of module FastMutexWithGoto: 36\n" + 
				"  line 122, col 27 to line 122, col 58 of module FastMutexWithGoto: 24\n" + 
				"  line 123, col 26 to line 123, col 41 of module FastMutexWithGoto: 0\n" + 
				"  line 127, col 17 to line 127, col 51 of module FastMutexWithGoto: 24\n" + 
				"  line 128, col 27 to line 128, col 42 of module FastMutexWithGoto: 0\n" + 
				"  line 132, col 16 to line 132, col 48 of module FastMutexWithGoto: 174\n" + 
				"  line 133, col 26 to line 133, col 41 of module FastMutexWithGoto: 0\n" + 
				"  line 136, col 17 to line 136, col 22 of module FastMutexWithGoto: 174\n" + 
				"  line 137, col 17 to line 137, col 49 of module FastMutexWithGoto: 174\n" + 
				"  line 138, col 27 to line 138, col 39 of module FastMutexWithGoto: 0\n" + 
				"  line 141, col 17 to line 141, col 47 of module FastMutexWithGoto: 258\n" + 
				"  line 142, col 17 to line 142, col 49 of module FastMutexWithGoto: 258\n" + 
				"  line 143, col 27 to line 143, col 39 of module FastMutexWithGoto: 0\n" + 
				"  line 64, col 17 to line 64, col 51 of module FastMutexWithGoto: 238\n" + 
				"  line 65, col 27 to line 65, col 42 of module FastMutexWithGoto: 0\n" + 
				"  line 68, col 19 to line 68, col 48 of module FastMutexWithGoto: 238\n" + 
				"  line 69, col 19 to line 69, col 50 of module FastMutexWithGoto: 238\n" + 
				"  line 70, col 29 to line 70, col 41 of module FastMutexWithGoto: 0\n" + 
				"  line 73, col 16 to line 73, col 24 of module FastMutexWithGoto: 238\n" + 
				"  line 74, col 16 to line 74, col 47 of module FastMutexWithGoto: 238\n" + 
				"  line 75, col 26 to line 75, col 38 of module FastMutexWithGoto: 0\n" + 
				"  line 79, col 27 to line 79, col 58 of module FastMutexWithGoto: 80\n" + 
				"  line 80, col 27 to line 80, col 58 of module FastMutexWithGoto: 152\n" + 
				"  line 81, col 26 to line 81, col 41 of module FastMutexWithGoto: 0\n" + 
				"  line 84, col 16 to line 84, col 46 of module FastMutexWithGoto: 164\n" + 
				"  line 85, col 16 to line 85, col 47 of module FastMutexWithGoto: 164\n" + 
				"  line 86, col 26 to line 86, col 38 of module FastMutexWithGoto: 0\n" + 
				"  line 90, col 16 to line 90, col 50 of module FastMutexWithGoto: 84\n" + 
				"  line 91, col 26 to line 91, col 41 of module FastMutexWithGoto: 0\n" + 
				"  line 94, col 16 to line 94, col 24 of module FastMutexWithGoto: 198\n" + 
				"  line 95, col 16 to line 95, col 47 of module FastMutexWithGoto: 198\n" + 
				"  line 96, col 26 to line 96, col 38 of module FastMutexWithGoto: 0");
	}
}
