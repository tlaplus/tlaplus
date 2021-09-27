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
 *   loki der quaeler - initial API and implementation
 *   Markus Alexander Kuppe
 ******************************************************************************/
package tlc2.tool.coverage;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

public class CCoverageTest extends AbstractCoverageTest {

    public CCoverageTest () {
        super("C");
    }

    @Test
    public void testSpec () {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "17"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "253", "20", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
		assertCoverage("<Init line 14, col 1 to line 14, col 4 of module C>: 3:3\n" + 
				"  line 14, col 12 to line 14, col 21 of module C: 1\n" + 
				"  line 15, col 12 to line 15, col 16 of module C: 3\n" + 
				"<A line 17, col 1 to line 17, col 1 of module C>: 16:20\n" + 
				"  line 17, col 9 to line 17, col 17 of module C: 40\n" + 
				"  |line 17, col 9 to line 17, col 9 of module C: 20\n" + 
				"  |line 17, col 15 to line 17, col 17 of module C: 20\n" + 
				"  line 18, col 9 to line 18, col 17 of module C: 40\n" + 
				"  |line 18, col 9 to line 18, col 9 of module C: 20\n" + 
				"  |line 18, col 15 to line 18, col 17 of module C: 20\n" + 
				"  line 19, col 9 to line 19, col 17 of module C: 20\n" + 
				"  line 20, col 9 to line 20, col 19 of module C: 20\n" + 
				"<B line 22, col 1 to line 22, col 1 of module C>: 0:20\n" + 
				"  line 22, col 9 to line 22, col 17 of module C: 40\n" + 
				"  |line 22, col 9 to line 22, col 9 of module C: 20\n" + 
				"  |line 22, col 15 to line 22, col 17 of module C: 20\n" + 
				"  line 12, col 30 to line 12, col 48 of module C: 640\n" + 
				"  line 12, col 19 to line 12, col 26 of module C: 20\n" + 
				"  line 23, col 12 to line 23, col 15 of module C: 20\n" + 
				"  line 24, col 9 to line 24, col 25 of module C: 20\n" + 
				"<C line 26, col 1 to line 26, col 1 of module C>: 0:0\n" + 
				"  line 26, col 9 to line 26, col 14 of module C: 20\n" + 
				"  line 27, col 9 to line 27, col 17 of module C: 0\n" + 
				"  line 28, col 9 to line 28, col 18 of module C: 0\n" + 
				"<D line 30, col 1 to line 30, col 1 of module C>: 1:210\n" + 
				"  line 30, col 6 to line 30, col 16 of module C: 210\n" + 
				"  |line 30, col 13 to line 30, col 16 of module C: 20\n" + 
				"  line 30, col 21 to line 30, col 31 of module C: 210\n" + 
				"<U1 line 32, col 1 to line 32, col 2 of module C>: 0:0\n" + 
				"  line 32, col 7 to line 32, col 11 of module C: 20\n" + 
				"  line 32, col 16 to line 32, col 29 of module C: 0\n" + 
				"<U2 line 34, col 1 to line 34, col 2 of module C>: 0:0\n" + 
				"  line 34, col 7 to line 34, col 11 of module C: 20\n" + 
				"  line 34, col 16 to line 34, col 32 of module C: 0\n" + 
				"<U3 line 36, col 1 to line 36, col 2 of module C>: 0:0\n" + 
				"  line 36, col 7 to line 36, col 11 of module C: 20\n" + 
				"  line 36, col 16 to line 36, col 26 of module C: 0\n" + 
				"  line 36, col 31 to line 36, col 41 of module C: 0\n" + 
				"<Inv line 48, col 1 to line 48, col 3 of module C>\n" + 
				"  line 48, col 8 to line 54, col 26 of module C: 21\n" + 
				"  |line 48, col 11 to line 48, col 19 of module C: 21\n" + 
				"  |line 49, col 11 to line 49, col 19 of module C: 21\n" + 
				"  |line 50, col 11 to line 50, col 22 of module C: 21\n" + 
				"  ||line 46, col 17 to line 46, col 64 of module C: 21\n" + 
				"  |||line 46, col 42 to line 46, col 64 of module C: 5376\n" + 
				"  ||||line 46, col 55 to line 46, col 64 of module C: 21504\n" + 
				"  ||||line 46, col 51 to line 46, col 51 of module C: 5376\n" + 
				"  |||line 46, col 26 to line 46, col 38 of module C: 21:26880\n" + 
				"  ||||line 46, col 34 to line 46, col 37 of module C: 21\n" +
				"  |line 51, col 23 to line 51, col 26 of module C: 21\n" + 
				"  |line 52, col 14 to line 54, col 26 of module C: 21\n" + 
				"  ||line 52, col 17 to line 52, col 27 of module C: 21\n" + 
				"  ||line 53, col 17 to line 53, col 40 of module C: 21\n" + 
				"  |||line 53, col 32 to line 53, col 40 of module C: 105\n" + 
				"  |||line 53, col 26 to line 53, col 29 of module C: 21\n" + 
				"  ||line 54, col 17 to line 54, col 26 of module C: 21\n" + 
				"<Inv2 line 56, col 1 to line 56, col 4 of module C>\n" + 
				"  line 56, col 9 to line 62, col 27 of module C: 21\n" + 
				"  |line 56, col 12 to line 56, col 20 of module C: 21\n" + 
				"  |line 57, col 12 to line 57, col 20 of module C: 21\n" + 
				"  |line 58, col 12 to line 58, col 23 of module C: 21\n" + 
				"  ||line 46, col 17 to line 46, col 64 of module C: 21\n" + 
				"  |||line 46, col 42 to line 46, col 64 of module C: 10752\n" + 
				"  ||||line 46, col 55 to line 46, col 64 of module C: 48384\n" + 
				"  ||||line 46, col 51 to line 46, col 51 of module C: 10752\n" + 
				"  |||line 46, col 26 to line 46, col 38 of module C: 21:59136\n" + 
				"  ||||line 46, col 34 to line 46, col 37 of module C: 21\n" +
				"  |line 59, col 24 to line 59, col 27 of module C: 21\n" + 
				"  |line 60, col 15 to line 62, col 27 of module C: 21\n" + 
				"  ||line 60, col 15 to line 60, col 28 of module C: 21\n" + 
				"  ||line 61, col 17 to line 62, col 27 of module C: 21\n" + 
				"  |||line 61, col 32 to line 62, col 27 of module C: 105\n" + 
				"  |||line 61, col 26 to line 61, col 29 of module C: 21\n"
				+ "<Constraint line 42, col 1 to line 42, col 10 of module C>: 252:253\n" + 
				"  line 42, col 15 to line 42, col 20 of module C: 253");
    }
}
