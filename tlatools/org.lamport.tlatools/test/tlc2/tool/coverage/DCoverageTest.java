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

public class DCoverageTest extends AbstractCoverageTest {

    public DCoverageTest () {
        super("D");
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
		assertCoverage("<Init line 5, col 1 to line 5, col 4 of module D>: 1:1\n" + 
				"  line 5, col 9 to line 5, col 13 of module D: 1\n" + 
				"<A line 11, col 1 to line 11, col 1 of module D>: 1:3\n" + 
				"  line 11, col 6 to line 11, col 17 of module D: 3\n" + 
				"  |line 11, col 11 to line 11, col 17 of module D: 3\n" + 
				"  ||line 9, col 12 to line 9, col 47 of module D: 9\n" + 
				"  |||line 9, col 15 to line 9, col 19 of module D: 9\n" + 
				"  |||line 9, col 33 to line 9, col 47 of module D: 6\n" + 
				"<B line 13, col 1 to line 13, col 1 of module D>: 1:3\n" + 
				"  line 13, col 6 to line 13, col 17 of module D: 3\n" + 
				"  |line 13, col 11 to line 13, col 17 of module D: 3\n" + 
				"  ||line 9, col 12 to line 9, col 47 of module D: 27\n" + 
				"  |||line 9, col 15 to line 9, col 19 of module D: 27\n" + 
				"  |||line 9, col 33 to line 9, col 47 of module D: 24");
    }
}
