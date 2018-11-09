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

public class Either3Test extends PCalModelCheckerTestCase {

	public Either3Test() {
		super("Either3", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "9"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "12", "9", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "4"));
		
		assertCoverage("  line 31, col 15 to line 31, col 20 of module Either3: 1\n" + 
				"  line 32, col 15 to line 32, col 23 of module Either3: 1\n" + 
				"  line 33, col 25 to line 33, col 32 of module Either3: 0\n" + 
				"  line 34, col 15 to line 34, col 20 of module Either3: 1\n" + 
				"  line 35, col 15 to line 35, col 23 of module Either3: 1\n" + 
				"  line 36, col 25 to line 36, col 32 of module Either3: 0\n" + 
				"  line 37, col 15 to line 37, col 22 of module Either3: 1\n" + 
				"  line 38, col 15 to line 38, col 23 of module Either3: 1\n" + 
				"  line 39, col 25 to line 39, col 32 of module Either3: 0\n" + 
				"  line 42, col 9 to line 42, col 18 of module Either3: 1\n" + 
				"  line 43, col 9 to line 43, col 17 of module Either3: 1\n" + 
				"  line 44, col 19 to line 44, col 28 of module Either3: 0\n" + 
				"  line 47, col 9 to line 47, col 18 of module Either3: 1\n" + 
				"  line 48, col 9 to line 48, col 17 of module Either3: 1\n" + 
				"  line 49, col 19 to line 49, col 28 of module Either3: 0\n" + 
				"  line 53, col 15 to line 53, col 24 of module Either3: 2\n" + 
				"  line 55, col 15 to line 55, col 24 of module Either3: 1\n" + 
				"  line 60, col 9 to line 60, col 20 of module Either3: 3\n" + 
				"  line 61, col 19 to line 61, col 28 of module Either3: 0\n" + 
				"  line 65, col 41 to line 65, col 44 of module Either3: 0");
	}
}
