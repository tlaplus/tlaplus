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

public class MCoverageTest extends AbstractCoverageTest {

    public MCoverageTest () {
        super("M");
    }

    @Test
    public void testSpec () {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "37056", "192", "0"));

		// No 'general' errors recorded
		assertFalse(recorder.recorded(EC.GENERAL));

		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
		
		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
		assertCoverage("<Init line 16, col 1 to line 16, col 4 of module M>: 192:192\n"
				+ "  line 17, col 17 to line 17, col 39 of module M: 1:24\n"
				+ "  |line 17, col 18 to line 17, col 27 of module M: 1\n"
				+ "  |line 17, col 32 to line 17, col 38 of module M: 1\n"
				+ "  line 18, col 16 to line 18, col 31 of module M: 8:192\n"
				+ "  |line 18, col 17 to line 18, col 21 of module M: 8\n"
				+ "  |line 18, col 26 to line 18, col 30 of module M: 8\n"
				+ "  line 19, col 6 to line 19, col 19 of module M: 64\n"
				+ "  line 20, col 6 to line 20, col 21 of module M: 192\n"
				+"<Next line 22, col 1 to line 22, col 4 of module M>: 0:36864\n"
				+ "  line 23, col 6 to line 23, col 40 of module M: 1536\n"
				+ "  |line 23, col 18 to line 23, col 40 of module M: 192:4608\n"
				+ "  ||line 23, col 19 to line 23, col 28 of module M: 192\n"
				+ "  ||line 23, col 33 to line 23, col 39 of module M: 192\n"
				+ "  line 24, col 6 to line 24, col 32 of module M: 12288\n"
				+ "  |line 24, col 17 to line 24, col 32 of module M: 1536:36864\n"
				+ "  ||line 24, col 18 to line 24, col 22 of module M: 1536\n"
				+ "  ||line 24, col 27 to line 24, col 31 of module M: 1536\n"
				+ "  line 25, col 6 to line 25, col 20 of module M: 36864\n"
				+ "  |line 25, col 16 to line 25, col 20 of module M: 12288\n"
				+ "  line 26, col 6 to line 26, col 22 of module M: 36864");

    }
}
