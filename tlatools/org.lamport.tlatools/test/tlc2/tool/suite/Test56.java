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

public class Test56 extends SuiteTestCase {
	public Test56() {
		super("9", "6", "0", "3");
	}

	@Override
	protected void assertAdditionalCoverage() {
		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
		assertCoverage("<Init line 10, col 1 to line 10, col 4 of module test56>: 3:3\n"
				+ "  line 10, col 25 to line 10, col 29 of module test56: 3\n"
				+ "  line 10, col 18 to line 10, col 21 of module test56: 1\n"
				+ "<Next line 11, col 1 to line 11, col 4 of module test56>: 3:6\n"
				+ "  line 11, col 9 to line 11, col 16 of module test56: 6\n"
				+ "<Action line 14, col 15 to line 14, col 33 of module test56>\n"
				+ "  line 14, col 15 to line 14, col 33 of module test56: 6\n"
				+ "  |line 14, col 16 to line 14, col 30 of module test56: 6\n"
				+ "  ||line 14, col 16 to line 14, col 18 of module test56: 6\n"
				+ "  ||line 14, col 22 to line 14, col 30 of module test56: 6\n"
				+ "  |||line 8, col 14 to line 8, col 37 of module test56: 6\n"
				+ "  ||||line 8, col 15 to line 8, col 18 of module test56: 6\n"
				+ "  ||||line 8, col 24 to line 8, col 37 of module test56: 12");
	}
}
