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

public class GCoverageTest extends AbstractCoverageTest {

    public GCoverageTest () {
        super("G");
    }

    @Test
    public void testSpec () {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2", "1", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertCoverage("<Init line 6, col 1 to line 6, col 4 of module G>: 1:1\n" + 
				"  line 6, col 9 to line 6, col 20 of module G: 1\n" + 
				"<Next line 8, col 1 to line 8, col 4 of module G>: 0:1\n" + 
				"  line 8, col 12 to line 8, col 25 of module G: 1\n" + 
				"  line 9, col 12 to line 9, col 27 of module G: 2\n" + 
				"  line 10, col 12 to line 10, col 23 of module G: 2\n" + 
				"<Prop line 12, col 1 to line 12, col 4 of module G>\n" + 
				"  line 12, col 9 to line 12, col 20 of module G: 1\n" + 
				"  |line 8, col 12 to line 8, col 25 of module G: 1\n" + 
				"  |line 9, col 12 to line 9, col 27 of module G: 1\n" + 
				"  |line 10, col 12 to line 10, col 23 of module G: 1");
		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
    }
}
