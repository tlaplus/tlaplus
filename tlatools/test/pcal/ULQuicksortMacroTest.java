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

public class ULQuicksortMacroTest extends PCalModelCheckerTestCase {

	public ULQuicksortMacroTest() {
		super("ULQuicksortMacro", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "27"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "258"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "342", "258", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "11"));

	assertCoverage("  line 104, col 16 to line 104, col 28 of module ULQuicksortMacro: 27\n" +
		"  line 105, col 16 to line 105, col 23 of module ULQuicksortMacro: 27\n" +
		"  line 106, col 16 to line 111, col 33 of module ULQuicksortMacro: 27\n" +
		"  line 112, col 13 to line 112, col 22 of module ULQuicksortMacro: 27\n" +
		"  line 113, col 13 to line 113, col 25 of module ULQuicksortMacro: 27\n" +
		"  line 114, col 23 to line 114, col 40 of module ULQuicksortMacro: 0\n" +
		"  line 118, col 41 to line 118, col 44 of module ULQuicksortMacro: 0\n" +
		"  line 64, col 29 to line 64, col 44 of module ULQuicksortMacro: 112\n" +
		"  line 70, col 31 to line 70, col 37 of module ULQuicksortMacro: 112\n" +
		"  line 71, col 24 to line 71, col 42 of module ULQuicksortMacro: 112\n" +
		"  line 72, col 24 to line 72, col 36 of module ULQuicksortMacro: 112\n" +
		"  line 73, col 34 to line 73, col 54 of module ULQuicksortMacro: 0\n" +
		"  line 74, col 24 to line 74, col 43 of module ULQuicksortMacro: 64\n" +
		"  line 75, col 24 to line 75, col 49 of module ULQuicksortMacro: 64\n" +
		"  line 76, col 24 to line 76, col 45 of module ULQuicksortMacro: 64\n" +
		"  line 77, col 24 to line 77, col 45 of module ULQuicksortMacro: 64\n" +
		"  line 78, col 24 to line 78, col 43 of module ULQuicksortMacro: 64\n" +
		"  line 79, col 34 to line 79, col 51 of module ULQuicksortMacro: 0\n" +
		"  line 82, col 16 to line 82, col 27 of module ULQuicksortMacro: 48\n" +
		"  line 83, col 16 to line 83, col 25 of module ULQuicksortMacro: 48\n" +
		"  line 84, col 16 to line 89, col 33 of module ULQuicksortMacro: 48\n" +
		"  line 90, col 13 to line 90, col 22 of module ULQuicksortMacro: 48\n" +
		"  line 91, col 13 to line 91, col 25 of module ULQuicksortMacro: 48\n" +
		"  line 92, col 23 to line 92, col 40 of module ULQuicksortMacro: 0\n" +
		"  line 95, col 16 to line 95, col 25 of module ULQuicksortMacro: 44\n" +
		"  line 96, col 16 to line 96, col 30 of module ULQuicksortMacro: 44\n" +
		"  line 97, col 13 to line 97, col 22 of module ULQuicksortMacro: 44\n" +
		"  line 98, col 13 to line 98, col 25 of module ULQuicksortMacro: 44\n" +
		"  line 99, col 23 to line 99, col 47 of module ULQuicksortMacro: 0");
	}
}
