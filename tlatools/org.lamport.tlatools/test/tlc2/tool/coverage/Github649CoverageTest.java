/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved. 
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

public class Github649CoverageTest extends AbstractCoverageTest {

    public Github649CoverageTest () {
        super("Github649");
    }

    @Test
    public void testSpec () {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "2"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "3", "2", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertCoverage("<Init line 14, col 1 to line 14, col 4 of module Github649>: 1:1\n"
				+ "  line 12, col 21 to line 12, col 25 of module Github649: 2\n"
				+ "  line 12, col 32 to line 12, col 37 of module Github649: 1\n"
				+ "  line 12, col 44 to line 12, col 60 of module Github649: 1\n"
				+ "  line 14, col 21 to line 14, col 25 of module Github649: 1\n"
				+ "<Next line 16, col 1 to line 16, col 4 of module Github649>: 1:2\n"
				+ "  line 16, col 9 to line 16, col 23 of module Github649: 2\n"
				+ "<TypeOK line 9, col 1 to line 9, col 6 of module Github649>\n"
				+ "  line 9, col 11 to line 9, col 24 of module Github649: 2\n"
				+ "  |line 7, col 15 to line 7, col 62 of module Github649: 4\n"
				+ "  ||line 7, col 18 to line 7, col 22 of module Github649: 4\n"
				+ "  ||line 7, col 29 to line 7, col 41 of module Github649: 2\n"
				+ "  ||line 7, col 48 to line 7, col 62 of module Github649: 2\n"
				+ "  |line 9, col 17 to line 9, col 21 of module Github649: 2\n"
				+ "<Constraint line 18, col 1 to line 18, col 10 of module Github649>: 3:3\n"
				+ "  line 19, col 5 to line 19, col 26 of module Github649: 3\n"
				+ "  |line 12, col 18 to line 12, col 60 of module Github649: 9\n"
				+ "  ||line 12, col 21 to line 12, col 25 of module Github649: 9\n"
				+ "  ||line 12, col 32 to line 12, col 37 of module Github649: 3\n"
				+ "  ||line 12, col 44 to line 12, col 60 of module Github649: 6\n"
				+ "  |line 19, col 10 to line 19, col 14 of module Github649: 3\n"
				+ "  |line 19, col 17 to line 19, col 22 of module Github649: 3");
		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
    }
}
