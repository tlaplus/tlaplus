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

public class BakeryTest extends PCalModelCheckerTestCase {

	public BakeryTest() {
		super("Bakery", "pcal");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "1183", "668", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "41"));
		
		assertCoverage("  line 102, col 32 to line 102, col 62 of module Bakery: 108\n" + 
				"  line 103, col 27 to line 103, col 58 of module Bakery: 108\n" + 
				"  line 104, col 27 to line 104, col 58 of module Bakery: 61\n" + 
				"  line 105, col 27 to line 105, col 36 of module Bakery: 61\n" + 
				"  line 106, col 26 to line 106, col 55 of module Bakery: 0\n" + 
				"  line 113, col 16 to line 113, col 76 of module Bakery: 61\n" + 
				"  line 114, col 16 to line 114, col 47 of module Bakery: 61\n" + 
				"  line 115, col 26 to line 115, col 54 of module Bakery: 0\n" + 
				"  line 119, col 16 to line 119, col 49 of module Bakery: 61\n" + 
				"  line 120, col 26 to line 120, col 60 of module Bakery: 0\n" + 
				"  line 123, col 18 to line 123, col 48 of module Bakery: 61\n" + 
				"  line 124, col 18 to line 124, col 51 of module Bakery: 61\n" + 
				"  line 125, col 28 to line 125, col 57 of module Bakery: 0\n" + 
				"  line 68, col 18 to line 68, col 61 of module Bakery: 166\n" + 
				"  line 69, col 18 to line 69, col 57 of module Bakery: 166\n" + 
				"  line 70, col 18 to line 70, col 48 of module Bakery: 166\n" + 
				"  line 71, col 18 to line 71, col 49 of module Bakery: 166\n" + 
				"  line 72, col 28 to line 72, col 41 of module Bakery: 0\n" + 
				"  line 78, col 43 to line 78, col 78 of module Bakery: 60\n" + 
				"  line 80, col 43 to line 80, col 52 of module Bakery: 52\n" + 
				"  line 81, col 32 to line 81, col 82 of module Bakery: 112\n" + 
				"  line 82, col 27 to line 82, col 58 of module Bakery: 112\n" + 
				"  line 83, col 27 to line 83, col 58 of module Bakery: 180\n" + 
				"  line 84, col 37 to line 84, col 51 of module Bakery: 0\n" + 
				"  line 85, col 26 to line 85, col 49 of module Bakery: 0\n" + 
				"  line 88, col 16 to line 88, col 58 of module Bakery: 180\n" + 
				"  line 89, col 16 to line 89, col 47 of module Bakery: 180\n" + 
				"  line 90, col 26 to line 90, col 55 of module Bakery: 0\n" + 
				"  line 93, col 16 to line 93, col 60 of module Bakery: 192\n" + 
				"  line 94, col 16 to line 94, col 55 of module Bakery: 192\n" + 
				"  line 95, col 16 to line 95, col 47 of module Bakery: 192\n" + 
				"  line 96, col 26 to line 96, col 44 of module Bakery: 0");
	}
}
