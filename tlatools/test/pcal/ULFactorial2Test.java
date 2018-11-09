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

public class ULFactorial2Test extends PCalModelCheckerTestCase {

	public ULFactorial2Test() {
		super("ULFactorial2", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "9"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "10", "9", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "9"));

	assertCoverage("  line 100, col 13 to line 100, col 18 of module ULFactorial2: 1\n" +
		"  line 101, col 13 to line 101, col 25 of module ULFactorial2: 1\n" +
		"  line 102, col 23 to line 102, col 44 of module ULFactorial2: 0\n" +
		"  line 108, col 13 to line 108, col 24 of module ULFactorial2: 1\n" +
		"  line 109, col 23 to line 109, col 60 of module ULFactorial2: 0\n" +
		"  line 113, col 41 to line 113, col 44 of module ULFactorial2: 0\n" +
		"  line 53, col 24 to line 53, col 43 of module ULFactorial2: 0\n" +
		"  line 54, col 24 to line 54, col 41 of module ULFactorial2: 0\n" +
		"  line 55, col 24 to line 55, col 47 of module ULFactorial2: 0\n" +
		"  line 56, col 24 to line 56, col 43 of module ULFactorial2: 0\n" +
		"  line 57, col 34 to line 57, col 55 of module ULFactorial2: 0\n" +
		"  line 58, col 24 to line 58, col 46 of module ULFactorial2: 3\n" +
		"  line 59, col 27 to line 59, col 42 of module ULFactorial2: 3\n" +
		"  line 60, col 27 to line 64, col 50 of module ULFactorial2: 3\n" +
		"  line 65, col 27 to line 65, col 44 of module ULFactorial2: 3\n" +
		"  line 66, col 24 to line 66, col 30 of module ULFactorial2: 3\n" +
		"  line 67, col 24 to line 67, col 36 of module ULFactorial2: 3\n" +
		"  line 68, col 24 to line 68, col 35 of module ULFactorial2: 3\n" +
		"  line 74, col 24 to line 74, col 43 of module ULFactorial2: 1\n" +
		"  line 75, col 24 to line 75, col 43 of module ULFactorial2: 1\n" +
		"  line 76, col 24 to line 76, col 47 of module ULFactorial2: 1\n" +
		"  line 77, col 24 to line 77, col 43 of module ULFactorial2: 1\n" +
		"  line 78, col 34 to line 78, col 54 of module ULFactorial2: 0\n" +
		"  line 79, col 24 to line 79, col 46 of module ULFactorial2: 2\n" +
		"  line 80, col 27 to line 80, col 42 of module ULFactorial2: 2\n" +
		"  line 81, col 27 to line 85, col 50 of module ULFactorial2: 2\n" +
		"  line 86, col 27 to line 86, col 46 of module ULFactorial2: 2\n" +
		"  line 87, col 24 to line 87, col 29 of module ULFactorial2: 2\n" +
		"  line 88, col 24 to line 88, col 36 of module ULFactorial2: 2\n" +
		"  line 89, col 24 to line 89, col 35 of module ULFactorial2: 2\n" +
		"  line 94, col 16 to line 94, col 24 of module ULFactorial2: 1\n" +
		"  line 95, col 16 to line 99, col 33 of module ULFactorial2: 1");
	}
}
