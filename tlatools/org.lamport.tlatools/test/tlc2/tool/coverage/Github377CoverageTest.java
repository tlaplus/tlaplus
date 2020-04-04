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

public class Github377CoverageTest extends AbstractCoverageTest {

    public Github377CoverageTest () {
        super("Github377");
    }

    @Test
    public void testSpec () {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2", "1", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertCoverage("<Action line 5, col 9 to line 5, col 16 of module Github377>: 1:1\n" + 
				"  line 5, col 9 to line 5, col 16 of module Github377: 1\n" + 
				"<Action line 5, col 24 to line 5, col 34 of module Github377>: 0:1\n" + 
				"  line 5, col 24 to line 5, col 34 of module Github377: 1\n" + 
				"<1Inv line 9, col 1 to line 9, col 4 of module Github377>\n" + 
				"  line 10, col 6 to line 10, col 69 of module Github377: 1\n" + 
				"  line 11, col 5 to line 11, col 13 of module Github377: 1\n" + 
				"<1InvNonRec line 15, col 1 to line 15, col 10 of module Github377>\n" + 
				"  line 16, col 6 to line 16, col 40 of module Github377: 1\n" + 
				"  line 17, col 5 to line 17, col 13 of module Github377: 1\n" + 
				"<2Inv line 21, col 1 to line 21, col 4 of module Github377>\n" + 
				"  line 25, col 10 to line 25, col 47 of module Github377: 1\n" + 
				"  line 26, col 7 to line 26, col 11 of module Github377: 1\n" + 
				"<2aInv line 28, col 1 to line 28, col 5 of module Github377>\n" + 
				"  line 32, col 10 to line 33, col 21 of module Github377: 1\n" + 
				"  line 34, col 7 to line 34, col 11 of module Github377: 1\n" + 
				"<2bInv line 36, col 1 to line 36, col 5 of module Github377>\n" + 
				"  line 40, col 10 to line 40, col 31 of module Github377: 1\n" + 
				"  line 41, col 7 to line 41, col 11 of module Github377: 1\n" + 
				"<3aInv line 44, col 1 to line 44, col 5 of module Github377>\n" + 
				"  line 48, col 10 to line 50, col 21 of module Github377: 1\n" + 
				"  line 51, col 7 to line 51, col 11 of module Github377: 1\n" + 
				"<3bInv line 55, col 1 to line 55, col 5 of module Github377>\n" + 
				"  line 58, col 11 to line 58, col 42 of module Github377: 1\n" + 
				"  line 57, col 11 to line 57, col 70 of module Github377: 1\n" + 
				"  line 60, col 13 to line 60, col 31 of module Github377: 1\n" + 
				"  line 61, col 7 to line 61, col 11 of module Github377: 1\n" + 
				"<4Inv line 66, col 1 to line 66, col 4 of module Github377>\n" + 
				"  line 71, col 11 to line 71, col 18 of module Github377: 1\n" + 
				"  line 72, col 7 to line 72, col 11 of module Github377: 1");
		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
    }
}
