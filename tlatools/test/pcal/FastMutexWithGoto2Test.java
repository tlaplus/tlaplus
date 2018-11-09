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

public class FastMutexWithGoto2Test extends PCalModelCheckerTestCase {

	public FastMutexWithGoto2Test() {
		super("FastMutexWithGoto2", "pcal", new String[] {"-wfNext"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "15900"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "42277", "15900", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "47"));

		assertCoverage("  line 102, col 16 to line 102, col 46 of module FastMutexWithGoto2: 2394\n" + 
				"  line 103, col 16 to line 103, col 54 of module FastMutexWithGoto2: 2394\n" + 
				"  line 104, col 16 to line 104, col 47 of module FastMutexWithGoto2: 2394\n" + 
				"  line 105, col 26 to line 105, col 35 of module FastMutexWithGoto2: 0\n" + 
				"  line 111, col 32 to line 111, col 70 of module FastMutexWithGoto2: 4140\n" + 
				"  line 112, col 27 to line 112, col 58 of module FastMutexWithGoto2: 4140\n" + 
				"  line 113, col 27 to line 113, col 59 of module FastMutexWithGoto2: 1890\n" + 
				"  line 114, col 27 to line 114, col 32 of module FastMutexWithGoto2: 1890\n" + 
				"  line 115, col 26 to line 115, col 38 of module FastMutexWithGoto2: 0\n" + 
				"  line 119, col 28 to line 119, col 60 of module FastMutexWithGoto2: 1458\n" + 
				"  line 120, col 28 to line 120, col 59 of module FastMutexWithGoto2: 432\n" + 
				"  line 121, col 27 to line 121, col 42 of module FastMutexWithGoto2: 0\n" + 
				"  line 125, col 17 to line 125, col 51 of module FastMutexWithGoto2: 672\n" + 
				"  line 126, col 27 to line 126, col 42 of module FastMutexWithGoto2: 0\n" + 
				"  line 130, col 16 to line 130, col 48 of module FastMutexWithGoto2: 2049\n" + 
				"  line 131, col 26 to line 131, col 41 of module FastMutexWithGoto2: 0\n" + 
				"  line 134, col 17 to line 134, col 22 of module FastMutexWithGoto2: 2049\n" + 
				"  line 135, col 17 to line 135, col 49 of module FastMutexWithGoto2: 2049\n" + 
				"  line 136, col 27 to line 136, col 39 of module FastMutexWithGoto2: 0\n" + 
				"  line 139, col 17 to line 139, col 47 of module FastMutexWithGoto2: 4209\n" + 
				"  line 140, col 17 to line 140, col 51 of module FastMutexWithGoto2: 4209\n" + 
				"  line 141, col 27 to line 141, col 39 of module FastMutexWithGoto2: 0\n" + 
				"  line 61, col 19 to line 61, col 50 of module FastMutexWithGoto2: 3234\n" + 
				"  line 62, col 29 to line 62, col 44 of module FastMutexWithGoto2: 0\n" + 
				"  line 65, col 16 to line 65, col 45 of module FastMutexWithGoto2: 3234\n" + 
				"  line 66, col 16 to line 66, col 47 of module FastMutexWithGoto2: 3234\n" + 
				"  line 67, col 26 to line 67, col 38 of module FastMutexWithGoto2: 0\n" + 
				"  line 70, col 16 to line 70, col 24 of module FastMutexWithGoto2: 3234\n" + 
				"  line 71, col 16 to line 71, col 47 of module FastMutexWithGoto2: 3234\n" + 
				"  line 72, col 26 to line 72, col 38 of module FastMutexWithGoto2: 0\n" + 
				"  line 76, col 27 to line 76, col 58 of module FastMutexWithGoto2: 1716\n" + 
				"  line 77, col 27 to line 77, col 58 of module FastMutexWithGoto2: 1539\n" + 
				"  line 78, col 26 to line 78, col 41 of module FastMutexWithGoto2: 0\n" + 
				"  line 81, col 16 to line 81, col 46 of module FastMutexWithGoto2: 2811\n" + 
				"  line 82, col 16 to line 82, col 47 of module FastMutexWithGoto2: 2811\n" + 
				"  line 83, col 26 to line 83, col 38 of module FastMutexWithGoto2: 0\n" + 
				"  line 87, col 16 to line 87, col 50 of module FastMutexWithGoto2: 1095\n" + 
				"  line 88, col 26 to line 88, col 41 of module FastMutexWithGoto2: 0\n" + 
				"  line 91, col 16 to line 91, col 24 of module FastMutexWithGoto2: 2487\n" + 
				"  line 92, col 16 to line 92, col 47 of module FastMutexWithGoto2: 2487\n" + 
				"  line 93, col 26 to line 93, col 38 of module FastMutexWithGoto2: 0\n" + 
				"  line 97, col 27 to line 97, col 58 of module FastMutexWithGoto2: 2394\n" + 
				"  line 98, col 27 to line 98, col 58 of module FastMutexWithGoto2: 1239\n" + 
				"  line 99, col 26 to line 99, col 41 of module FastMutexWithGoto2: 0");
	}
}
