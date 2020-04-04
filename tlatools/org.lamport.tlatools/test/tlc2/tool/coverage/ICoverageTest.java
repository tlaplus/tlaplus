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

public class ICoverageTest extends AbstractCoverageTest {

    public ICoverageTest () {
        super("I");
    }

    @Test
    public void testSpec () {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "20", "5", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertCoverage("<Action line 11, col 9 to line 11, col 25 of module I>: 5:5\n" + 
				"  line 11, col 9 to line 11, col 25 of module I: 5\n" + 
				"  |line 11, col 15 to line 11, col 25 of module I: 1:6\n" + 
				"<Action line 11, col 52 to line 11, col 55 of module I>: 0:15\n" + 
				"  line 11, col 52 to line 11, col 52 of module I: 15\n" +
				"  |line 8, col 1 to line 9, col 22 of module I: 15\n" + 
				"  ||line 9, col 8 to line 9, col 22 of module I: 15\n" + 
				"  ||line 8, col 9 to line 8, col 15 of module I: 15\n" + 
				"  line 11, col 54 to line 11, col 54 of module I: 15\n" +
				"<Inv line 13, col 1 to line 13, col 3 of module I>\n" + 
				"  line 13, col 8 to line 13, col 34 of module I: 5\n" + 
				"  |line 13, col 27 to line 13, col 34 of module I: 15\n" + 
				"  |line 13, col 17 to line 13, col 24 of module I: 5");
		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
    }
}
