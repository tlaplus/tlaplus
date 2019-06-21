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

public class ACoverageTest extends AbstractCoverageTest {

    public ACoverageTest () {
        super("A");
    }

    @Test
    public void testSpec () {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "2"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "7", "3", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
		assertCoverage("<Init line 7, col 1 to line 7, col 4 of module A>: 1:1\n" + 
				"  line 7, col 12 to line 7, col 16 of module A: 1\n" + 
				"  line 8, col 12 to line 8, col 21 of module A: 1\n" + 
				"  |line 5, col 11 to line 5, col 49 of module A: 1\n" + 
				"  ||line 5, col 31 to line 5, col 49 of module A: 131072\n" + 
				"  ||line 5, col 20 to line 5, col 27 of module A: 1\n" + // This used to be a level deeper and value 131072
				"  |line 8, col 16 to line 8, col 20 of module A: 1\n" + 
				"<A line 13, col 1 to line 13, col 4 of module A>: 1:3\n" + 
				"  line 13, col 9 to line 13, col 19 of module A: 3\n" + 
				"  |line 13, col 14 to line 13, col 19 of module A: 3\n" + 
				"  ||line 11, col 11 to line 11, col 61 of module A: 3\n" + 
				"  |||line 11, col 31 to line 11, col 61 of module A: 30\n" + 
				"  ||||line 11, col 57 to line 11, col 61 of module A: 162\n" + 
				"  ||||line 11, col 41 to line 11, col 52 of module A: 30\n" + 
				"  |||line 11, col 24 to line 11, col 27 of module A: 3\n" + 
				"  ||line 13, col 18 to line 13, col 18 of module A: 3\n" + 
				"<B line 15, col 1 to line 15, col 4 of module A>: 1:3\n" + 
				"  line 15, col 9 to line 15, col 19 of module A: 3\n" + 
				"  |line 15, col 14 to line 15, col 19 of module A: 3\n" + 
				"  ||line 11, col 11 to line 11, col 61 of module A: 3\n" + 
				"  |||line 11, col 31 to line 11, col 61 of module A: 9\n" + 
				"  ||||line 11, col 57 to line 11, col 61 of module A: 15\n" + 
				"  ||||line 11, col 41 to line 11, col 52 of module A: 9\n" + 
				"  |||line 11, col 24 to line 11, col 27 of module A: 3\n" + 
				"  ||line 15, col 18 to line 15, col 18 of module A: 3");
    }
}
