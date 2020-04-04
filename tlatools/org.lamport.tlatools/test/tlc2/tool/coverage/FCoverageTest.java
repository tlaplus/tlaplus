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

public class FCoverageTest extends AbstractCoverageTest {

    public FCoverageTest () {
        super("F");
    }

    @Test
    public void testSpec () {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "4", "2", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
		assertCoverage("<Init line 8, col 1 to line 8, col 4 of module F>: 2:2\n" + 
				"  line 8, col 9 to line 8, col 79 of module F: 2\n" + 
				"  |line 8, col 15 to line 8, col 79 of module F: 1\n" + 
				"  ||line 6, col 25 to line 6, col 56 of module F: 1:3\n" + 
				"  |||line 6, col 37 to line 6, col 54 of module F: 5\n" + 
				"  ||||line 6, col 37 to line 6, col 40 of module F: 5\n" + 
				"  ||||line 6, col 45 to line 6, col 54 of module F: 4\n" + 
				"  |||||line 6, col 47 to line 6, col 47 of module F: 4\n" + 
				"  |||||line 6, col 50 to line 6, col 53 of module F: 2\n" + 
				"  |||||line 8, col 63 to line 8, col 78 of module F: 4\n" + 
				"  ||||||line 8, col 63 to line 8, col 73 of module F: 4\n" + 
				"  ||||||line 8, col 78 to line 8, col 78 of module F: 2\n" + 
				"  |||line 6, col 33 to line 6, col 33 of module F: 1\n" + 
				"  ||line 8, col 18 to line 8, col 28 of module F: 1:6\n" + 
				"  ||line 8, col 41 to line 8, col 45 of module F: 5\n" + 
				"  ||line 8, col 63 to line 8, col 78 of module F: 4\n" + 
				"  |||line 8, col 63 to line 8, col 73 of module F: 4\n" + 
				"  |||line 8, col 78 to line 8, col 78 of module F: 2\n" + 
				"<Next line 10, col 1 to line 10, col 4 of module F>: 0:2\n" + 
				"  line 10, col 9 to line 10, col 19 of module F: 2");
    }
}
