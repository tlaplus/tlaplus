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
package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class CoverageStatisticsTest extends ModelCheckerTestCase {

    public CoverageStatisticsTest () {
        super("CoverageStatistics", new String[] {"-coverage", "9999"}); // To not interfere with testing, 9999 to make sure only final coverage is reported.
    }

    @Test
    public void testSpec () {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "17"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "41", "19", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertCoverage("  line 17, col 9 to line 17, col 17 of module CoverageStatistics: 19\n" + 
				"  line 18, col 19 to line 18, col 19 of module CoverageStatistics: 19\n" + 
				"  line 21, col 19 to line 21, col 25 of module CoverageStatistics: 0\n" + 
				"  line 21, col 23 to line 21, col 23 of module CoverageStatistics: 19\n" + 
				"  line 24, col 9 to line 24, col 17 of module CoverageStatistics: 0\n" + 
				"  line 25, col 9 to line 25, col 18 of module CoverageStatistics: 0\n" + 
				"  line 27, col 26 to line 27, col 29 of module CoverageStatistics: 0\n" + 
				"  line 29, col 26 to line 29, col 32 of module CoverageStatistics: 0\n" + 
				"  line 31, col 26 to line 31, col 26 of module CoverageStatistics: 0\n" + 
				"  line 31, col 41 to line 31, col 41 of module CoverageStatistics: 0");
    }
}
