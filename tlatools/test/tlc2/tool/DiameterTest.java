/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
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
package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class DiameterTest extends ModelCheckerTestCase {

	public DiameterTest() {
		super("DieHardTLA");
	}

	@Test
	public void testSpec() {
		// ModelChecker has finished without errors and generated the expected
		// amount of states
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "97", "16", "0"));

		// The diameter is known to be 8 as reported by TLC running with a
		// single worker. With multiple workers, it's possible to get a higher
		// or a lower number.
		final int level = recorder.getRecordAsInt(EC.TLC_SEARCH_DEPTH);
		assertTrue(String.format("Level below threshold: %s", level), level >= 8);

		assertCoverage("  line 12, col 17 to line 12, col 26 of module DieHardTLA: 16\n" +
			"  line 13, col 17 to line 13, col 28 of module DieHardTLA: 16\n" +
			"  line 15, col 15 to line 15, col 24 of module DieHardTLA: 16\n" +
			"  line 16, col 15 to line 16, col 28 of module DieHardTLA: 16\n" +
			"  line 18, col 18 to line 18, col 27 of module DieHardTLA: 16\n" +
			"  line 19, col 18 to line 19, col 29 of module DieHardTLA: 16\n" +
			"  line 21, col 16 to line 21, col 25 of module DieHardTLA: 16\n" +
			"  line 22, col 16 to line 22, col 29 of module DieHardTLA: 16\n" +
			"  line 25, col 24 to line 25, col 43 of module DieHardTLA: 11\n" +
			"  line 26, col 24 to line 26, col 33 of module DieHardTLA: 11\n" +
			"  line 27, col 24 to line 27, col 33 of module DieHardTLA: 5\n" +
			"  line 28, col 24 to line 28, col 49 of module DieHardTLA: 5\n" +
			"  line 31, col 24 to line 31, col 33 of module DieHardTLA: 7\n" +
			"  line 32, col 24 to line 32, col 43 of module DieHardTLA: 7\n" +
			"  line 33, col 24 to line 33, col 49 of module DieHardTLA: 9\n" +
			"  line 34, col 24 to line 34, col 33 of module DieHardTLA: 9");
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ModelCheckerTestCase#getNumberOfThreads()
	 */
	@Override
	protected int getNumberOfThreads() {
		return 4;
	}
}
