/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
 * Copyright (c) 2026 NVIDIA Corporation. All rights reserved.
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
package tlc2.tool.suite;

import static org.junit.Assert.assertFalse;

import tlc2.output.EC;

public class Test63 extends SuiteTestCase {
	public Test63() {
		super("696", "216", "0", "72");
	}

	@Override
	protected void assertAdditionalCoverage() {
		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
		assertCoverage("<BigInit line 37, col 1 to line 37, col 7 of module test63>: 72:72\n"
				+ "  line 37, col 15 to line 37, col 19 of module test63: 1\n"
				+ "  line 39, col 15 to line 39, col 26 of module test63: 72\n"
				+ "  |line 39, col 23 to line 39, col 26 of module test63: 12\n"
				+ "<BigNext line 24, col 1 to line 24, col 7 of module test63>: 144:624\n"
				+ "  line 21, col 15 to line 21, col 45 of module test63: 264\n"
				+ "  |line 21, col 24 to line 21, col 45 of module test63: 216:624\n"
				+ "  ||line 21, col 38 to line 21, col 44 of module test63: 1296\n"
				+ "  ||line 21, col 31 to line 21, col 34 of module test63: 216\n"
				+ "  line 22, col 15 to line 22, col 26 of module test63: 264\n"
				+ "  line 24, col 25 to line 24, col 27 of module test63: 216\n"
				+ "  line 5, col 12 to line 5, col 46 of module test63a: 144\n"
				+ "  |line 5, col 18 to line 5, col 46 of module test63a: 624\n"
				+ "  ||line 5, col 21 to line 5, col 27 of module test63a: 624\n"
				+ "  ||line 5, col 34 to line 5, col 39 of module test63a: 572\n"
				+ "  line 25, col 23 to line 25, col 24 of module test63: 480\n"
				+ "  line 14, col 13 to line 14, col 50 of module test63: 624\n"
				+ "  |line 14, col 18 to line 14, col 50 of module test63: 840\n"
				+ "  ||line 14, col 21 to line 14, col 25 of module test63: 840\n"
				+ "  |||line 5, col 12 to line 5, col 46 of module test63a: 840\n"
				+ "  ||||line 5, col 12 to line 5, col 14 of module test63a: 840\n"
				+ "  ||||line 5, col 18 to line 5, col 46 of module test63a: 840\n"
				+ "  |||||line 5, col 21 to line 5, col 27 of module test63a: 840\n"
				+ "  |||||line 5, col 34 to line 5, col 39 of module test63a: 770\n"
				+ "  ||line 14, col 39 to line 14, col 50 of module test63: 624\n"
				+ "  line 27, col 15 to line 27, col 50 of module test63: 840\n"
				+ "  |line 27, col 15 to line 27, col 19 of module test63: 840\n"
				+ "  ||line 5, col 12 to line 5, col 46 of module test63a: 840\n"
				+ "  |||line 5, col 12 to line 5, col 14 of module test63a: 840\n"
				+ "  |||line 5, col 18 to line 5, col 46 of module test63a: 840\n"
				+ "  ||||line 5, col 21 to line 5, col 27 of module test63a: 840\n"
				+ "  ||||line 5, col 34 to line 5, col 39 of module test63a: 770\n"
				+ "  |line 27, col 24 to line 27, col 50 of module test63: 216\n"
				+ "  line 28, col 15 to line 28, col 43 of module test63: 768\n"
				+ "<TypeOK line 49, col 1 to line 49, col 6 of module test63>\n"
				+ "  line 49, col 11 to line 50, col 25 of module test63: 216\n"
				+ "<Action line 52, col 1 to line 52, col 21 of module test63>\n"
				+ "  line 52, col 1 to line 52, col 21 of module test63: 72\n"
				+ "  line 4, col 12 to line 4, col 27 of module test63a: 72\n"
				+ "<Action line 52, col 1 to line 52, col 21 of module test63>\n"
				+ "  line 52, col 1 to line 52, col 21 of module test63: 2208\n"
				+ "  line 6, col 20 to line 6, col 29 of module test63a: 624\n"
				+ "  |line 6, col 21 to line 6, col 25 of module test63a: 624\n"
				+ "  ||line 5, col 12 to line 5, col 46 of module test63a: 624\n"
				+ "  |||line 5, col 12 to line 5, col 14 of module test63a: 624\n"
				+ "  |||line 5, col 18 to line 5, col 46 of module test63a: 624\n"
				+ "  ||||line 5, col 21 to line 5, col 27 of module test63a: 624\n"
				+ "  ||||line 5, col 34 to line 5, col 39 of module test63a: 572\n"
				+ "  |line 6, col 28 to line 6, col 29 of module test63a: 960");
	}
}
