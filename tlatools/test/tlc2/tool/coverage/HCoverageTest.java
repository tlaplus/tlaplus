/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
package tlc2.tool.coverage;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

public class HCoverageTest extends AbstractCoverageTest {

    public HCoverageTest () {
        super("H");
    }

    @Test
    public void testSpec () {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "3"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "26", "6", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertCoverage("<Inv line 22, col 1 to line 22, col 3 of module H>: 1:31\n" + 
				"  line 22, col 11 to line 22, col 16 of module H: 1\n" + 
				"  line 23, col 11 to line 23, col 15 of module H: 31\n" + 
				"<A line 11, col 1 to line 11, col 1 of module H>: 1:6\n" + 
				"  line 11, col 6 to line 11, col 12 of module H: 6\n" + 
				"<BandC line 13, col 1 to line 13, col 5 of module H (13 13 14 28)>: 2:15\n" + 
				"  line 13, col 16 to line 13, col 26 of module H: 11\n" + 
				"  |line 13, col 16 to line 13, col 16 of module H: 6\n" + 
				"  |line 13, col 22 to line 13, col 26 of module H: 6\n" + 
				"  line 14, col 16 to line 14, col 28 of module H: 15\n" + 
				"  |line 14, col 23 to line 14, col 28 of module H: 5\n" + 
				"<BandC line 13, col 1 to line 13, col 5 of module H (15 13 16 22)>: 1:3\n" + 
				"  line 15, col 16 to line 15, col 21 of module H: 3\n" + 
				"  |line 15, col 16 to line 15, col 16 of module H: 6\n" + 
				"  line 16, col 16 to line 16, col 22 of module H: 3\n" + 
				"<DandE line 18, col 1 to line 18, col 5 of module H (18 11 18 27)>: 1:1\n" + 
				"  line 18, col 11 to line 18, col 16 of module H: 7\n" + 
				"  |line 18, col 11 to line 18, col 11 of module H: 6\n" + 
				"  line 18, col 21 to line 18, col 27 of module H: 1\n" + 
				"<DandE line 18, col 1 to line 18, col 5 of module H (18 34 18 53)>: 0:0\n" + 
				"  line 18, col 34 to line 18, col 40 of module H: 6\n" + 
				"  line 18, col 45 to line 18, col 53 of module H: 0");
		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
    }
}
