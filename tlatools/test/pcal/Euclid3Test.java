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

public class Euclid3Test extends PCalModelCheckerTestCase {

	public Euclid3Test() {
		super("Euclid3", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "3"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "94"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "97", "94", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "50"));

		assertCoverage("  line 38, col 35 to line 38, col 40 of module Euclid3: 0\n" + 
				"  line 39, col 35 to line 39, col 40 of module Euclid3: 0\n" + 
				"  line 41, col 42 to line 41, col 51 of module Euclid3: 0\n" + 
				"  line 42, col 21 to line 42, col 29 of module Euclid3: 44\n" + 
				"  line 44, col 21 to line 44, col 32 of module Euclid3: 3\n" + 
				"  line 45, col 31 to line 45, col 40 of module Euclid3: 0\n" + 
				"  line 46, col 10 to line 46, col 23 of module Euclid3: 47\n" + 
				"  line 49, col 9 to line 49, col 18 of module Euclid3: 44\n" + 
				"  line 50, col 9 to line 50, col 18 of module Euclid3: 44\n" + 
				"  line 51, col 19 to line 51, col 32 of module Euclid3: 0\n" + 
				"  line 55, col 41 to line 55, col 44 of module Euclid3: 0");
	}
}
