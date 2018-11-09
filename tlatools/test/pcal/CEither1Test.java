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

public class CEither1Test extends PCalModelCheckerTestCase {

	public CEither1Test() {
		super("CEither1", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "7"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "9", "7", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "4"));
		
		assertCoverage("  line 25, col 15 to line 25, col 20 of module CEither1: 1\n" + 
				"  line 26, col 15 to line 26, col 23 of module CEither1: 1\n" + 
				"  line 27, col 15 to line 27, col 20 of module CEither1: 1\n" + 
				"  line 28, col 15 to line 28, col 20 of module CEither1: 1\n" + 
				"  line 29, col 15 to line 29, col 23 of module CEither1: 1\n" + 
				"  line 30, col 15 to line 30, col 20 of module CEither1: 1\n" + 
				"  line 33, col 9 to line 33, col 18 of module CEither1: 1\n" + 
				"  line 34, col 9 to line 34, col 17 of module CEither1: 1\n" + 
				"  line 35, col 9 to line 35, col 14 of module CEither1: 1\n" + 
				"  line 38, col 9 to line 38, col 18 of module CEither1: 1\n" + 
				"  line 39, col 9 to line 39, col 17 of module CEither1: 1\n" + 
				"  line 40, col 9 to line 40, col 14 of module CEither1: 1\n" + 
				"  line 44, col 9 to line 44, col 20 of module CEither1: 2\n" + 
				"  line 45, col 19 to line 45, col 28 of module CEither1: 0\n" + 
				"  line 49, col 41 to line 49, col 44 of module CEither1: 0");
	}
}
