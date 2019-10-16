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
				"  line 11, col 5 to line 11, col 13 of module Github377: 1");
		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
    }
}
