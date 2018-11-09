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

public class CBakeryTest extends PCalModelCheckerTestCase {

	public CBakeryTest() {
		super("CBakery", "pcal");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "867", "486", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "31"));
		
		assertCoverage("  line 102, col 16 to line 102, col 76 of module CBakery: 39\n" + 
				"  line 103, col 16 to line 103, col 47 of module CBakery: 39\n" + 
				"  line 104, col 26 to line 104, col 54 of module CBakery: 0\n" + 
				"  line 108, col 16 to line 108, col 49 of module CBakery: 39\n" + 
				"  line 109, col 26 to line 109, col 60 of module CBakery: 0\n" + 
				"  line 112, col 18 to line 112, col 48 of module CBakery: 39\n" + 
				"  line 113, col 18 to line 113, col 51 of module CBakery: 39\n" + 
				"  line 114, col 28 to line 114, col 57 of module CBakery: 0\n" + 
				"  line 57, col 18 to line 57, col 61 of module CBakery: 114\n" + 
				"  line 58, col 18 to line 58, col 57 of module CBakery: 114\n" + 
				"  line 59, col 18 to line 59, col 48 of module CBakery: 114\n" + 
				"  line 60, col 18 to line 60, col 49 of module CBakery: 114\n" + 
				"  line 61, col 28 to line 61, col 41 of module CBakery: 0\n" + 
				"  line 67, col 43 to line 67, col 78 of module CBakery: 48\n" + 
				"  line 69, col 43 to line 69, col 52 of module CBakery: 46\n" + 
				"  line 70, col 32 to line 70, col 82 of module CBakery: 94\n" + 
				"  line 71, col 27 to line 71, col 58 of module CBakery: 94\n" + 
				"  line 72, col 27 to line 72, col 58 of module CBakery: 146\n" + 
				"  line 73, col 37 to line 73, col 51 of module CBakery: 0\n" + 
				"  line 74, col 26 to line 74, col 49 of module CBakery: 0\n" + 
				"  line 77, col 16 to line 77, col 58 of module CBakery: 146\n" + 
				"  line 78, col 16 to line 78, col 47 of module CBakery: 146\n" + 
				"  line 79, col 26 to line 79, col 55 of module CBakery: 0\n" + 
				"  line 82, col 16 to line 82, col 60 of module CBakery: 142\n" + 
				"  line 83, col 16 to line 83, col 55 of module CBakery: 142\n" + 
				"  line 84, col 16 to line 84, col 47 of module CBakery: 142\n" + 
				"  line 85, col 26 to line 85, col 44 of module CBakery: 0\n" + 
				"  line 91, col 32 to line 91, col 62 of module CBakery: 68\n" + 
				"  line 92, col 27 to line 92, col 58 of module CBakery: 68\n" + 
				"  line 93, col 27 to line 93, col 58 of module CBakery: 39\n" + 
				"  line 94, col 27 to line 94, col 36 of module CBakery: 39\n" + 
				"  line 95, col 26 to line 95, col 55 of module CBakery: 0");
	}
}
