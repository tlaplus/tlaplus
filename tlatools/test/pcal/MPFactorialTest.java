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

public class MPFactorialTest extends PCalModelCheckerTestCase {

	public MPFactorialTest() {
		super("MPFactorial", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "729"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "1946", "729", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "25"));

	assertCoverage("  line 105, col 70 to line 105, col 73 of module MPFactorial: 0\n" +
		"  line 50, col 27 to line 50, col 74 of module MPFactorial: 243\n" +
		"  line 51, col 27 to line 51, col 71 of module MPFactorial: 243\n" +
		"  line 52, col 27 to line 52, col 80 of module MPFactorial: 243\n" +
		"  line 53, col 27 to line 53, col 77 of module MPFactorial: 243\n" +
		"  line 54, col 37 to line 54, col 42 of module MPFactorial: 243\n" +
		"  line 55, col 27 to line 55, col 87 of module MPFactorial: 1215\n" +
		"  line 56, col 27 to line 56, col 72 of module MPFactorial: 1215\n" +
		"  line 57, col 27 to line 57, col 53 of module MPFactorial: 1215\n" +
		"  line 58, col 27 to line 58, col 58 of module MPFactorial: 1215\n" +
		"  line 59, col 27 to line 59, col 40 of module MPFactorial: 1215\n" +
		"  line 64, col 19 to line 64, col 51 of module MPFactorial: 162\n" +
		"  line 65, col 19 to line 69, col 67 of module MPFactorial: 162\n" +
		"  line 70, col 16 to line 70, col 42 of module MPFactorial: 162\n" +
		"  line 71, col 16 to line 71, col 47 of module MPFactorial: 162\n" +
		"  line 72, col 26 to line 72, col 31 of module MPFactorial: 162\n" +
		"  line 77, col 16 to line 77, col 49 of module MPFactorial: 162\n" +
		"  line 78, col 26 to line 78, col 53 of module MPFactorial: 0\n" +
		"  line 83, col 13 to line 83, col 42 of module MPFactorial: 81\n" +
		"  line 84, col 13 to line 88, col 55 of module MPFactorial: 81\n" +
		"  line 89, col 10 to line 89, col 33 of module MPFactorial: 81\n" +
		"  line 90, col 10 to line 90, col 38 of module MPFactorial: 81\n" +
		"  line 91, col 20 to line 91, col 25 of module MPFactorial: 81\n" +
		"  line 96, col 10 to line 96, col 40 of module MPFactorial: 81\n" +
		"  line 97, col 20 to line 97, col 47 of module MPFactorial: 0");
	}
}
