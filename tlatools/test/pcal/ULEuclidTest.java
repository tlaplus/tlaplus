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

public class ULEuclidTest extends PCalModelCheckerTestCase {

	public ULEuclidTest() {
		super("ULEuclid", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "400"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "6352"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "6752", "6352", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "42"));

	assertCoverage("  line 59, col 38 to line 59, col 43 of module ULEuclid: 698\n" +
		"  line 60, col 38 to line 60, col 43 of module ULEuclid: 698\n" +
		"  line 62, col 45 to line 62, col 54 of module ULEuclid: 0\n" +
		"  line 63, col 24 to line 63, col 36 of module ULEuclid: 2776\n" +
		"  line 66, col 24 to line 66, col 35 of module ULEuclid: 400\n" +
		"  line 67, col 34 to line 67, col 43 of module ULEuclid: 0\n" +
		"  line 68, col 23 to line 68, col 40 of module ULEuclid: 0\n" +
		"  line 71, col 13 to line 71, col 22 of module ULEuclid: 2776\n" +
		"  line 72, col 13 to line 72, col 25 of module ULEuclid: 2776\n" +
		"  line 73, col 23 to line 73, col 43 of module ULEuclid: 0\n" +
		"  line 77, col 41 to line 77, col 44 of module ULEuclid: 0");
	}
}
