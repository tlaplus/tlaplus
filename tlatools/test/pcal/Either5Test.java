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

public class Either5Test extends PCalModelCheckerTestCase {

	public Either5Test() {
		super("Either5", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "7"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "10", "7", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "3"));

		assertCoverage("  line 36, col 9 to line 36, col 18 of module Either5: 1\n" + 
				"  line 37, col 9 to line 37, col 28 of module Either5: 1\n" + 
				"  line 38, col 9 to line 38, col 26 of module Either5: 1\n" + 
				"  line 39, col 9 to line 39, col 28 of module Either5: 1\n" + 
				"  line 40, col 19 to line 40, col 28 of module Either5: 0\n" + 
				"  line 45, col 16 to line 45, col 21 of module Either5: 1\n" + 
				"  line 46, col 16 to line 46, col 21 of module Either5: 1\n" + 
				"  line 47, col 16 to line 47, col 24 of module Either5: 1\n" + 
				"  line 48, col 26 to line 48, col 37 of module Either5: 0\n" + 
				"  line 49, col 16 to line 49, col 21 of module Either5: 1\n" + 
				"  line 50, col 16 to line 50, col 24 of module Either5: 1\n" + 
				"  line 51, col 26 to line 51, col 40 of module Either5: 0\n" + 
				"  line 52, col 19 to line 52, col 24 of module Either5: 1\n" + 
				"  line 53, col 19 to line 56, col 36 of module Either5: 1\n" + 
				"  line 57, col 16 to line 57, col 24 of module Either5: 1\n" + 
				"  line 58, col 26 to line 58, col 33 of module Either5: 0\n" + 
				"  line 59, col 10 to line 59, col 15 of module Either5: 3\n" + 
				"  line 63, col 9 to line 63, col 17 of module Either5: 1\n" + 
				"  line 64, col 19 to line 64, col 41 of module Either5: 0\n" + 
				"  line 68, col 9 to line 68, col 20 of module Either5: 2\n" + 
				"  line 69, col 19 to line 69, col 41 of module Either5: 0\n" + 
				"  line 73, col 41 to line 73, col 44 of module Either5: 0");
	}
}
