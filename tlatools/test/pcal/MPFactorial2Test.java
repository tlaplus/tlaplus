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

public class MPFactorial2Test extends PCalModelCheckerTestCase {

	public MPFactorial2Test() {
		super("MPFactorial2", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "1728"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "4754", "1728", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "34"));

		assertCoverage("  line 100, col 31 to line 100, col 78 of module MPFactorial2: 864\n" +
			"  line 101, col 28 to line 101, col 54 of module MPFactorial2: 864\n" +
			"  line 102, col 28 to line 102, col 59 of module MPFactorial2: 864\n" +
			"  line 103, col 28 to line 103, col 39 of module MPFactorial2: 864\n" +
			"  line 108, col 19 to line 108, col 51 of module MPFactorial2: 288\n" +
			"  line 109, col 19 to line 113, col 67 of module MPFactorial2: 288\n" +
			"  line 114, col 16 to line 114, col 42 of module MPFactorial2: 288\n" +
			"  line 115, col 16 to line 115, col 47 of module MPFactorial2: 288\n" +
			"  line 116, col 26 to line 116, col 47 of module MPFactorial2: 0\n" +
			"  line 121, col 16 to line 121, col 49 of module MPFactorial2: 288\n" +
			"  line 122, col 26 to line 122, col 63 of module MPFactorial2: 0\n" +
			"  line 127, col 13 to line 127, col 42 of module MPFactorial2: 144\n" +
			"  line 128, col 13 to line 132, col 55 of module MPFactorial2: 144\n" +
			"  line 133, col 10 to line 133, col 33 of module MPFactorial2: 144\n" +
			"  line 134, col 10 to line 134, col 38 of module MPFactorial2: 144\n" +
			"  line 135, col 20 to line 135, col 41 of module MPFactorial2: 0\n" +
			"  line 140, col 10 to line 140, col 40 of module MPFactorial2: 144\n" +
			"  line 141, col 20 to line 141, col 57 of module MPFactorial2: 0\n" +
			"  line 149, col 70 to line 149, col 73 of module MPFactorial2: 0\n" +
			"  line 61, col 27 to line 61, col 74 of module MPFactorial2: 0\n" +
			"  line 62, col 27 to line 62, col 71 of module MPFactorial2: 0\n" +
			"  line 63, col 27 to line 63, col 80 of module MPFactorial2: 0\n" +
			"  line 64, col 27 to line 64, col 77 of module MPFactorial2: 0\n" +
			"  line 65, col 37 to line 65, col 58 of module MPFactorial2: 0\n" +
			"  line 66, col 27 to line 66, col 87 of module MPFactorial2: 1296\n" +
			"  line 67, col 30 to line 67, col 75 of module MPFactorial2: 1296\n" +
			"  line 68, col 30 to line 72, col 78 of module MPFactorial2: 1296\n" +
			"  line 73, col 27 to line 73, col 55 of module MPFactorial2: 1296\n" +
			"  line 74, col 27 to line 74, col 59 of module MPFactorial2: 1296\n" +
			"  line 75, col 37 to line 75, col 49 of module MPFactorial2: 0\n" +
			"  line 78, col 15 to line 78, col 62 of module MPFactorial2: 1296\n" +
			"  line 79, col 15 to line 79, col 59 of module MPFactorial2: 1296\n" +
			"  line 80, col 15 to line 80, col 68 of module MPFactorial2: 1296\n" +
			"  line 81, col 15 to line 81, col 65 of module MPFactorial2: 1296\n" +
			"  line 82, col 25 to line 82, col 46 of module MPFactorial2: 0\n" +
			"  line 88, col 28 to line 88, col 75 of module MPFactorial2: 432\n" +
			"  line 89, col 28 to line 89, col 75 of module MPFactorial2: 432\n" +
			"  line 90, col 28 to line 90, col 81 of module MPFactorial2: 432\n" +
			"  line 91, col 28 to line 91, col 78 of module MPFactorial2: 432\n" +
			"  line 92, col 38 to line 92, col 58 of module MPFactorial2: 0\n" +
			"  line 93, col 28 to line 93, col 88 of module MPFactorial2: 864\n" +
			"  line 94, col 31 to line 94, col 76 of module MPFactorial2: 864\n" +
			"  line 95, col 31 to line 99, col 85 of module MPFactorial2: 864");
	}
}
