/*******************************************************************************
 * Copyright (c) 2022 Microsoft Research. All rights reserved. 
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

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github648wNTest extends ModelCheckerTestCase {

	public Github648wNTest() {
		super("Github648", ExitStatus.SUCCESS);
	}

	@Override
	protected int getNumberOfThreads() {
		return 10;
	}

	protected boolean doDump() {
		return false;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));

		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "1332", "36", "0"));
		
		assertCoverage("<Init line 34, col 1 to line 34, col 4 of module Github648>: 36:36\n"
				+ "  line 35, col 8 to line 35, col 23 of module Github648: 1\n"
				+ "  line 36, col 8 to line 36, col 23 of module Github648: 36\n"
				+ "  |line 36, col 14 to line 36, col 23 of module Github648: 6\n"
				+ "<Next line 38, col 1 to line 38, col 4 of module Github648>: 0:1296\n"
				+ "  line 39, col 8 to line 39, col 24 of module Github648: 216\n"
				+ "  |line 39, col 15 to line 39, col 24 of module Github648: 36\n"
				+ "  line 40, col 8 to line 40, col 24 of module Github648: 1296\n"
				+ "  |line 40, col 15 to line 40, col 24 of module Github648: 216\n"
				+ "<Inv line 42, col 1 to line 42, col 3 of module Github648>\n"
				+ "  line 43, col 5 to line 49, col 62 of module Github648: 36\n"
				+ "  |line 43, col 8 to line 43, col 23 of module Github648: 36\n"
				+ "  |line 44, col 8 to line 44, col 27 of module Github648: 36\n"
				+ "  |line 45, col 8 to line 45, col 23 of module Github648: 36\n"
				+ "  |line 46, col 8 to line 46, col 27 of module Github648: 36\n"
				+ "  |line 47, col 8 to line 49, col 62 of module Github648: 36\n"
				+ "  ||line 47, col 8 to line 49, col 54 of module Github648: 36\n"
				+ "  |||line 47, col 16 to line 49, col 53 of module Github648: 1\n"
				+ "  ||||line 48, col 9 to line 49, col 52 of module Github648: 1\n"
				+ "  |||||line 48, col 17 to line 49, col 51 of module Github648: 10\n"
				+ "  ||||||line 13, col 3 to line 13, col 34 of module Github648: 10\n"
				+ "  |||||||line 13, col 9 to line 13, col 34 of module Github648: 10:131290\n"
				+ "  ||||||||line 13, col 10 to line 13, col 20 of module Github648: 40:2674464\n"
				+ "  |||||||||line 13, col 11 to line 13, col 14 of module Github648: 40\n"
				+ "  |||||||||line 13, col 19 to line 13, col 19 of module Github648: 40\n"
				+ "  ||||||||line 13, col 30 to line 13, col 33 of module Github648: 10\n"
				+ "  ||||||line 49, col 17 to line 49, col 47 of module Github648: 10\n"
				+ "  |||||||line 49, col 25 to line 49, col 46 of module Github648: 10\n"
				+ "  ||||||||line 13, col 3 to line 13, col 34 of module Github648: 10\n"
				+ "  |||||||||line 13, col 9 to line 13, col 34 of module Github648: 10:690148\n"
				+ "  ||||||||||line 13, col 10 to line 13, col 20 of module Github648: 40:1473\n"
				+ "  |||||||||||line 13, col 11 to line 13, col 14 of module Github648: 40\n"
				+ "  |||||||||||line 13, col 19 to line 13, col 19 of module Github648: 40\n"
				+ "  ||||||||||line 13, col 30 to line 13, col 33 of module Github648: 10\n"
				+ "  ||||||||line 49, col 36 to line 49, col 42 of module Github648: 10:750");
	}
}
