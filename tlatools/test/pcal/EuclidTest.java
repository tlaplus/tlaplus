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

public class EuclidTest extends PCalModelCheckerTestCase {

	public EuclidTest() {
		super("Euclid", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "400"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "6352"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "6752", "6352", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "42"));

		assertCoverage("  line 60, col 34 to line 60, col 39 of module Euclid: 698\n" + 
				"  line 61, col 34 to line 61, col 39 of module Euclid: 698\n" + 
				"  line 63, col 41 to line 63, col 50 of module Euclid: 0\n" + 
				"  line 64, col 20 to line 64, col 28 of module Euclid: 2776\n" + 
				"  line 67, col 20 to line 67, col 31 of module Euclid: 400\n" + 
				"  line 68, col 30 to line 68, col 39 of module Euclid: 0\n" + 
				"  line 69, col 19 to line 69, col 36 of module Euclid: 0\n" + 
				"  line 72, col 9 to line 72, col 18 of module Euclid: 2776\n" + 
				"  line 73, col 9 to line 73, col 17 of module Euclid: 2776\n" + 
				"  line 74, col 19 to line 74, col 39 of module Euclid: 0\n" + 
				"  line 78, col 41 to line 78, col 44 of module Euclid: 0");
	}
}
