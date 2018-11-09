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

public class CCallReturn1Test extends PCalModelCheckerTestCase {

	public CCallReturn1Test() {
		super("CCallReturn1", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "8"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "9", "8", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "8"));
		
		assertCoverage("  line 102, col 13 to line 102, col 21 of module CCallReturn1: 1\n" + 
				"  line 103, col 13 to line 107, col 30 of module CCallReturn1: 1\n" + 
				"  line 108, col 10 to line 108, col 15 of module CCallReturn1: 1\n" + 
				"  line 109, col 10 to line 109, col 19 of module CCallReturn1: 1\n" + 
				"  line 110, col 20 to line 110, col 38 of module CCallReturn1: 0\n" + 
				"  line 114, col 41 to line 114, col 44 of module CCallReturn1: 0\n" + 
				"  line 49, col 10 to line 49, col 15 of module CCallReturn1: 1\n" + 
				"  line 50, col 13 to line 50, col 26 of module CCallReturn1: 1\n" + 
				"  line 51, col 13 to line 55, col 30 of module CCallReturn1: 1\n" + 
				"  line 56, col 10 to line 56, col 16 of module CCallReturn1: 1\n" + 
				"  line 57, col 10 to line 57, col 19 of module CCallReturn1: 1\n" + 
				"  line 58, col 20 to line 58, col 35 of module CCallReturn1: 0\n" + 
				"  line 63, col 13 to line 63, col 29 of module CCallReturn1: 1\n" + 
				"  line 64, col 13 to line 68, col 36 of module CCallReturn1: 1\n" + 
				"  line 69, col 13 to line 69, col 30 of module CCallReturn1: 1\n" + 
				"  line 70, col 10 to line 70, col 16 of module CCallReturn1: 1\n" + 
				"  line 71, col 10 to line 71, col 19 of module CCallReturn1: 1\n" + 
				"  line 72, col 20 to line 72, col 35 of module CCallReturn1: 0\n" + 
				"  line 80, col 13 to line 80, col 28 of module CCallReturn1: 2\n" + 
				"  line 81, col 13 to line 84, col 36 of module CCallReturn1: 2\n" + 
				"  line 85, col 13 to line 85, col 30 of module CCallReturn1: 2\n" + 
				"  line 86, col 10 to line 86, col 19 of module CCallReturn1: 2\n" + 
				"  line 87, col 20 to line 87, col 38 of module CCallReturn1: 0\n" + 
				"  line 94, col 10 to line 94, col 29 of module CCallReturn1: 2\n" + 
				"  line 95, col 10 to line 95, col 33 of module CCallReturn1: 2\n" + 
				"  line 96, col 10 to line 96, col 29 of module CCallReturn1: 2\n" + 
				"  line 97, col 20 to line 97, col 41 of module CCallReturn1: 0");
	}
}
