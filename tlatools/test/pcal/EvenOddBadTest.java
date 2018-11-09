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

public class EvenOddBadTest extends PCalModelCheckerTestCase {

	public EvenOddBadTest() {
		super("EvenOddBad", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "2"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "13"));
		assertTrue(recorder.recorded(EC.TLC_CHECKING_TEMPORAL_PROPS_END));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "15", "13", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "9"));

		assertCoverage("  line 102, col 41 to line 102, col 44 of module EvenOddBad: 0\n" + 
				"  line 44, col 24 to line 44, col 37 of module EvenOddBad: 2\n" + 
				"  line 45, col 24 to line 45, col 33 of module EvenOddBad: 2\n" + 
				"  line 46, col 34 to line 46, col 50 of module EvenOddBad: 0\n" + 
				"  line 47, col 27 to line 50, col 44 of module EvenOddBad: 2\n" + 
				"  line 51, col 27 to line 51, col 43 of module EvenOddBad: 2\n" + 
				"  line 52, col 24 to line 52, col 35 of module EvenOddBad: 2\n" + 
				"  line 53, col 34 to line 53, col 39 of module EvenOddBad: 2\n" + 
				"  line 54, col 13 to line 54, col 26 of module EvenOddBad: 4\n" + 
				"  line 57, col 10 to line 57, col 29 of module EvenOddBad: 2\n" + 
				"  line 58, col 10 to line 58, col 35 of module EvenOddBad: 2\n" + 
				"  line 59, col 10 to line 59, col 29 of module EvenOddBad: 2\n" + 
				"  line 60, col 20 to line 60, col 37 of module EvenOddBad: 0\n" + 
				"  line 66, col 23 to line 66, col 37 of module EvenOddBad: 0\n" + 
				"  line 67, col 23 to line 67, col 32 of module EvenOddBad: 0\n" + 
				"  line 68, col 33 to line 68, col 50 of module EvenOddBad: 0\n" + 
				"  line 69, col 26 to line 72, col 43 of module EvenOddBad: 2\n" + 
				"  line 73, col 26 to line 73, col 42 of module EvenOddBad: 2\n" + 
				"  line 74, col 23 to line 74, col 35 of module EvenOddBad: 2\n" + 
				"  line 75, col 33 to line 75, col 38 of module EvenOddBad: 2\n" + 
				"  line 76, col 12 to line 76, col 23 of module EvenOddBad: 2\n" + 
				"  line 79, col 10 to line 79, col 29 of module EvenOddBad: 1\n" + 
				"  line 80, col 10 to line 80, col 33 of module EvenOddBad: 1\n" + 
				"  line 81, col 10 to line 81, col 29 of module EvenOddBad: 1\n" + 
				"  line 82, col 20 to line 82, col 38 of module EvenOddBad: 0\n" + 
				"  line 87, col 13 to line 90, col 30 of module EvenOddBad: 2\n" + 
				"  line 91, col 13 to line 91, col 22 of module EvenOddBad: 2\n" + 
				"  line 92, col 10 to line 92, col 22 of module EvenOddBad: 2\n" + 
				"  line 93, col 20 to line 93, col 37 of module EvenOddBad: 0\n" + 
				"  line 97, col 10 to line 97, col 21 of module EvenOddBad: 1\n" + 
				"  line 98, col 20 to line 98, col 51 of module EvenOddBad: 0");
	}
}
