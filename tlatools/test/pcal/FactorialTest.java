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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package pcal;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

public class FactorialTest extends PCalModelCheckerTestCase {

	public FactorialTest() {
		super("Factorial", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "9"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "10", "9", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "9"));

		assertCoverage("  line 39, col 21 to line 39, col 40 of module Factorial: 1\n" + 
				"  line 40, col 21 to line 40, col 38 of module Factorial: 1\n" + 
				"  line 41, col 21 to line 41, col 44 of module Factorial: 1\n" + 
				"  line 42, col 21 to line 42, col 40 of module Factorial: 1\n" + 
				"  line 43, col 31 to line 43, col 36 of module Factorial: 1\n" + 
				"  line 44, col 21 to line 44, col 43 of module Factorial: 5\n" + 
				"  line 45, col 21 to line 45, col 36 of module Factorial: 5\n" + 
				"  line 46, col 21 to line 46, col 26 of module Factorial: 5\n" + 
				"  line 47, col 21 to line 47, col 30 of module Factorial: 5\n" + 
				"  line 48, col 21 to line 48, col 34 of module Factorial: 5\n" + 
				"  line 53, col 13 to line 53, col 21 of module Factorial: 1\n" + 
				"  line 54, col 13 to line 58, col 30 of module Factorial: 1\n" + 
				"  line 59, col 10 to line 59, col 15 of module Factorial: 1\n" + 
				"  line 60, col 10 to line 60, col 19 of module Factorial: 1\n" + 
				"  line 61, col 20 to line 61, col 25 of module Factorial: 1\n" + 
				"  line 65, col 10 to line 65, col 21 of module Factorial: 1\n" + 
				"  line 66, col 20 to line 66, col 47 of module Factorial: 0\n" + 
				"  line 70, col 41 to line 70, col 44 of module Factorial: 0");
	}
}
