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

public class CoverageStatisticsTest extends AbstractCoverageTest {

    public CoverageStatisticsTest () {
        super("CoverageStatistics");
    }

    @Test
    public void testSpec () {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "17"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "98", "19", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertCoverage("<Init line 12, col 1 to line 12, col 4 of module CoverageStatistics>: 3:3\n" + 
				"  line 12, col 12 to line 12, col 21 of module CoverageStatistics: 1\n" + 
				"  line 13, col 12 to line 13, col 16 of module CoverageStatistics: 3\n" + 
				"<A line 15, col 1 to line 15, col 1 of module CoverageStatistics>: 16:19\n" + 
				"  line 15, col 9 to line 15, col 17 of module CoverageStatistics: 38\n" + 
				"  |line 15, col 9 to line 15, col 9 of module CoverageStatistics: 19\n" + 
				"  |line 15, col 15 to line 15, col 17 of module CoverageStatistics: 19\n" + 
				"  line 16, col 9 to line 16, col 17 of module CoverageStatistics: 38\n" + 
				"  |line 16, col 9 to line 16, col 9 of module CoverageStatistics: 19\n" + 
				"  |line 16, col 15 to line 16, col 17 of module CoverageStatistics: 19\n" + 
				"  line 17, col 9 to line 17, col 17 of module CoverageStatistics: 19\n" + 
				"  line 18, col 9 to line 18, col 19 of module CoverageStatistics: 19\n" + 
				"<B line 20, col 1 to line 20, col 1 of module CoverageStatistics>: 0:19\n" + 
				"  line 20, col 9 to line 20, col 17 of module CoverageStatistics: 38\n" + 
				"  |line 20, col 9 to line 20, col 9 of module CoverageStatistics: 19\n" + 
				"  |line 20, col 15 to line 20, col 17 of module CoverageStatistics: 19\n" + 
				"  line 21, col 9 to line 21, col 25 of module CoverageStatistics: 19\n" + 
				"<C line 26, col 1 to line 26, col 1 of module CoverageStatistics>: 0:0\n" + 
				"  line 26, col 9 to line 26, col 14 of module CoverageStatistics: 19\n" + 
				"  line 27, col 9 to line 27, col 17 of module CoverageStatistics: 0\n" + 
				"  line 28, col 9 to line 28, col 18 of module CoverageStatistics: 0\n" + 
				"<U1 line 30, col 1 to line 30, col 2 of module CoverageStatistics>: 0:0\n" + 
				"  line 30, col 7 to line 30, col 11 of module CoverageStatistics: 19\n" + 
				"  line 30, col 16 to line 30, col 29 of module CoverageStatistics: 0\n" + 
				"<U2 line 32, col 1 to line 32, col 2 of module CoverageStatistics>: 0:0\n" + 
				"  line 32, col 7 to line 32, col 11 of module CoverageStatistics: 19\n" + 
				"  line 32, col 16 to line 32, col 32 of module CoverageStatistics: 0\n" + 
				"<U3 line 34, col 1 to line 34, col 2 of module CoverageStatistics>: 0:0\n" + 
				"  line 34, col 7 to line 34, col 11 of module CoverageStatistics: 19\n" + 
				"  line 34, col 16 to line 34, col 26 of module CoverageStatistics: 0\n" + 
				"  line 34, col 31 to line 34, col 41 of module CoverageStatistics: 0\n" + 
				"<U4 line 36, col 1 to line 36, col 2 of module CoverageStatistics>: 0:0\n" + 
				"  line 36, col 7 to line 36, col 11 of module CoverageStatistics: 19\n" + 
				"  line 36, col 16 to line 36, col 26 of module CoverageStatistics: 0\n" + 
				"  line 36, col 31 to line 36, col 41 of module CoverageStatistics: 0\n" + 
				"<UC1 line 38, col 1 to line 38, col 3 of module CoverageStatistics>: 0:19\n" + 
				"  line 38, col 8 to line 38, col 16 of module CoverageStatistics: 38\n" + 
				"  |line 38, col 8 to line 38, col 8 of module CoverageStatistics: 19\n" + 
				"  |line 38, col 14 to line 38, col 16 of module CoverageStatistics: 19\n" + 
				"  line 38, col 21 to line 38, col 37 of module CoverageStatistics: 19\n" + 
				"<UC2 line 40, col 1 to line 40, col 3 of module CoverageStatistics>: 0:19\n" + 
				"  line 40, col 8 to line 40, col 16 of module CoverageStatistics: 38\n" + 
				"  |line 40, col 8 to line 40, col 8 of module CoverageStatistics: 19\n" + 
				"  |line 40, col 14 to line 40, col 16 of module CoverageStatistics: 19\n" + 
				"  line 40, col 21 to line 40, col 31 of module CoverageStatistics: 19\n" + 
				"  line 40, col 36 to line 40, col 46 of module CoverageStatistics: 19\n" + 
				"<UC3 line 42, col 1 to line 42, col 3 of module CoverageStatistics>: 0:19\n" + 
				"  line 42, col 8 to line 42, col 16 of module CoverageStatistics: 38\n" + 
				"  |line 42, col 8 to line 42, col 8 of module CoverageStatistics: 19\n" + 
				"  |line 42, col 14 to line 42, col 16 of module CoverageStatistics: 19\n" + 
				"  line 42, col 21 to line 42, col 34 of module CoverageStatistics: 19\n"
				+ "<Constraint line 48, col 1 to line 48, col 10 of module CoverageStatistics>: 97:98\n" + 
				"  line 48, col 15 to line 48, col 20 of module CoverageStatistics: 98");
    }
}
