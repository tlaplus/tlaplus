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

public class Test52 extends SuiteTestCase {
	public Test52() {
		super("3", "2", "0", "1");
	}

	@Override
	protected void assertAdditionalCoverage() {
		assertFalse(recorder.recorded(EC.TLC_COVERAGE_MISMATCH));
		assertCoverage("<Init line 33, col 1 to line 33, col 4 of module test52>: 1:1\n"
				+ "  line 33, col 9 to line 34, col 20 of module test52: 1\n"
				+ "<Next line 35, col 1 to line 35, col 4 of module test52>: 1:2\n"
				+ "  line 35, col 12 to line 35, col 27 of module test52: 2\n"
				+ "  |line 35, col 16 to line 35, col 27 of module test52: 2\n"
				+ "  ||line 35, col 16 to line 35, col 16 of module test52: 2\n"
				+ "  ||line 35, col 23 to line 35, col 27 of module test52: 2:4\n"
				+ "  line 36, col 12 to line 36, col 27 of module test52: 2\n"
				+ "  |line 36, col 16 to line 36, col 27 of module test52: 2\n"
				+ "  ||line 36, col 16 to line 36, col 16 of module test52: 2\n"
				+ "  ||line 36, col 23 to line 36, col 27 of module test52: 2:4\n"
				+ "<Action line 50, col 15 to line 50, col 38 of module test52>\n"
				+ "  line 50, col 15 to line 50, col 38 of module test52: 2\n"
				+ "  |line 50, col 16 to line 50, col 28 of module test52: 2\n"
				+ "  ||line 47, col 2 to line 48, col 16 of module test52: 2\n"
				+ "  |||line 47, col 5 to line 47, col 28 of module test52: 2\n"
				+ "  ||||line 40, col 26 to line 40, col 31 of module test52: 2\n"
				+ "  |||||line 40, col 30 to line 40, col 30 of module test52: 4\n"
				+ "  |||line 48, col 5 to line 48, col 16 of module test52: 2");
	}
}
