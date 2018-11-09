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

public class Factorial2Test extends PCalModelCheckerTestCase {

	public Factorial2Test() {
		super("Factorial2", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "12"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "13", "12", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "12"));

		assertCoverage("  line 100, col 13 to line 100, col 21 of module Factorial2: 1\n" + 
				"  line 101, col 13 to line 105, col 30 of module Factorial2: 1\n" + 
				"  line 106, col 10 to line 106, col 15 of module Factorial2: 1\n" + 
				"  line 107, col 10 to line 107, col 19 of module Factorial2: 1\n" + 
				"  line 108, col 20 to line 108, col 41 of module Factorial2: 0\n" + 
				"  line 114, col 10 to line 114, col 21 of module Factorial2: 1\n" + 
				"  line 115, col 20 to line 115, col 57 of module Factorial2: 0\n" + 
				"  line 119, col 41 to line 119, col 44 of module Factorial2: 0\n" + 
				"  line 53, col 21 to line 53, col 40 of module Factorial2: 0\n" + 
				"  line 54, col 21 to line 54, col 38 of module Factorial2: 0\n" + 
				"  line 55, col 21 to line 55, col 44 of module Factorial2: 0\n" + 
				"  line 56, col 21 to line 56, col 40 of module Factorial2: 0\n" + 
				"  line 57, col 31 to line 57, col 52 of module Factorial2: 0\n" + 
				"  line 58, col 21 to line 58, col 43 of module Factorial2: 3\n" + 
				"  line 59, col 24 to line 59, col 39 of module Factorial2: 3\n" + 
				"  line 60, col 24 to line 64, col 41 of module Factorial2: 3\n" + 
				"  line 65, col 21 to line 65, col 27 of module Factorial2: 3\n" + 
				"  line 66, col 21 to line 66, col 31 of module Factorial2: 3\n" + 
				"  line 67, col 31 to line 67, col 43 of module Factorial2: 0\n" + 
				"  line 70, col 9 to line 70, col 28 of module Factorial2: 3\n" + 
				"  line 71, col 9 to line 71, col 26 of module Factorial2: 3\n" + 
				"  line 72, col 9 to line 72, col 32 of module Factorial2: 3\n" + 
				"  line 73, col 9 to line 73, col 28 of module Factorial2: 3\n" + 
				"  line 74, col 19 to line 74, col 40 of module Factorial2: 0\n" + 
				"  line 80, col 22 to line 80, col 41 of module Factorial2: 1\n" + 
				"  line 81, col 22 to line 81, col 41 of module Factorial2: 1\n" + 
				"  line 82, col 22 to line 82, col 45 of module Factorial2: 1\n" + 
				"  line 83, col 22 to line 83, col 41 of module Factorial2: 1\n" + 
				"  line 84, col 32 to line 84, col 52 of module Factorial2: 0\n" + 
				"  line 85, col 22 to line 85, col 44 of module Factorial2: 2\n" + 
				"  line 86, col 25 to line 86, col 40 of module Factorial2: 2\n" + 
				"  line 87, col 25 to line 91, col 48 of module Factorial2: 2\n" + 
				"  line 92, col 25 to line 92, col 44 of module Factorial2: 2\n" + 
				"  line 93, col 22 to line 93, col 27 of module Factorial2: 2\n" + 
				"  line 94, col 22 to line 94, col 31 of module Factorial2: 2\n" + 
				"  line 95, col 22 to line 95, col 33 of module Factorial2: 2");
	}
}
