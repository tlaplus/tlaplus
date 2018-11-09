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

public class ULEvenOddTest extends PCalModelCheckerTestCase {

	public ULEvenOddTest() {
		super("ULEvenOdd", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "13"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "14", "13", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "13"));

	assertCoverage("  line 103, col 41 to line 103, col 44 of module ULEvenOdd: 0\n" +
		"  line 50, col 24 to line 50, col 37 of module ULEvenOdd: 1\n" +
		"  line 51, col 24 to line 51, col 43 of module ULEvenOdd: 1\n" +
		"  line 52, col 24 to line 52, col 49 of module ULEvenOdd: 1\n" +
		"  line 53, col 24 to line 53, col 43 of module ULEvenOdd: 1\n" +
		"  line 54, col 24 to line 54, col 35 of module ULEvenOdd: 1\n" +
		"  line 55, col 27 to line 58, col 50 of module ULEvenOdd: 3\n" +
		"  line 59, col 27 to line 59, col 43 of module ULEvenOdd: 3\n" +
		"  line 60, col 24 to line 60, col 36 of module ULEvenOdd: 3\n" +
		"  line 61, col 34 to line 61, col 52 of module ULEvenOdd: 0\n" +
		"  line 67, col 24 to line 67, col 38 of module ULEvenOdd: 0\n" +
		"  line 68, col 24 to line 68, col 36 of module ULEvenOdd: 0\n" +
		"  line 69, col 34 to line 69, col 51 of module ULEvenOdd: 0\n" +
		"  line 70, col 27 to line 73, col 44 of module ULEvenOdd: 3\n" +
		"  line 74, col 27 to line 74, col 43 of module ULEvenOdd: 3\n" +
		"  line 75, col 24 to line 75, col 36 of module ULEvenOdd: 3\n" +
		"  line 76, col 34 to line 76, col 39 of module ULEvenOdd: 3\n" +
		"  line 77, col 13 to line 77, col 24 of module ULEvenOdd: 3\n" +
		"  line 80, col 13 to line 80, col 32 of module ULEvenOdd: 3\n" +
		"  line 81, col 13 to line 81, col 36 of module ULEvenOdd: 3\n" +
		"  line 82, col 13 to line 82, col 32 of module ULEvenOdd: 3\n" +
		"  line 83, col 23 to line 83, col 41 of module ULEvenOdd: 0\n" +
		"  line 88, col 16 to line 91, col 33 of module ULEvenOdd: 1\n" +
		"  line 92, col 16 to line 92, col 25 of module ULEvenOdd: 1\n" +
		"  line 93, col 13 to line 93, col 25 of module ULEvenOdd: 1\n" +
		"  line 94, col 23 to line 94, col 40 of module ULEvenOdd: 0\n" +
		"  line 98, col 13 to line 98, col 24 of module ULEvenOdd: 1\n" +
		"  line 99, col 23 to line 99, col 54 of module ULEvenOdd: 0");
	}
}
