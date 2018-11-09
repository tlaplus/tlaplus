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

public class CallReturn2Test extends PCalModelCheckerTestCase {

	public CallReturn2Test() {
		super("CallReturn2", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "11"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "12", "11", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "11"));
		
		assertCoverage("  line 100, col 20 to line 100, col 51 of module CallReturn2: 0\n" + 
				"  line 112, col 22 to line 112, col 39 of module CallReturn2: 3\n" + 
				"  line 113, col 22 to line 113, col 28 of module CallReturn2: 3\n" + 
				"  line 114, col 22 to line 114, col 30 of module CallReturn2: 3\n" + 
				"  line 115, col 22 to line 115, col 32 of module CallReturn2: 3\n" + 
				"  line 116, col 22 to line 116, col 32 of module CallReturn2: 3\n" + 
				"  line 117, col 22 to line 117, col 35 of module CallReturn2: 3\n" + 
				"  line 118, col 22 to line 118, col 41 of module CallReturn2: 1\n" + 
				"  line 119, col 22 to line 119, col 41 of module CallReturn2: 1\n" + 
				"  line 120, col 22 to line 120, col 41 of module CallReturn2: 1\n" + 
				"  line 121, col 22 to line 121, col 41 of module CallReturn2: 1\n" + 
				"  line 122, col 22 to line 122, col 41 of module CallReturn2: 1\n" + 
				"  line 123, col 22 to line 123, col 35 of module CallReturn2: 1\n" + 
				"  line 124, col 21 to line 124, col 43 of module CallReturn2: 0\n" + 
				"  line 129, col 10 to line 129, col 15 of module CallReturn2: 0\n" + 
				"  line 130, col 10 to line 130, col 19 of module CallReturn2: 0\n" + 
				"  line 131, col 20 to line 131, col 65 of module CallReturn2: 0\n" + 
				"  line 134, col 13 to line 134, col 18 of module CallReturn2: 0\n" + 
				"  line 135, col 13 to line 138, col 36 of module CallReturn2: 0\n" + 
				"  line 139, col 13 to line 139, col 30 of module CallReturn2: 0\n" + 
				"  line 140, col 10 to line 140, col 19 of module CallReturn2: 0\n" + 
				"  line 141, col 20 to line 141, col 55 of module CallReturn2: 0\n" + 
				"  line 147, col 10 to line 147, col 29 of module CallReturn2: 0\n" + 
				"  line 148, col 10 to line 148, col 27 of module CallReturn2: 0\n" + 
				"  line 149, col 10 to line 149, col 29 of module CallReturn2: 0\n" + 
				"  line 150, col 20 to line 150, col 58 of module CallReturn2: 0\n" + 
				"  line 155, col 12 to line 155, col 17 of module CallReturn2: 1\n" + 
				"  line 156, col 12 to line 161, col 29 of module CallReturn2: 1\n" + 
				"  line 162, col 9 to line 162, col 16 of module CallReturn2: 1\n" + 
				"  line 163, col 9 to line 163, col 18 of module CallReturn2: 1\n" + 
				"  line 164, col 9 to line 164, col 18 of module CallReturn2: 1\n" + 
				"  line 165, col 19 to line 165, col 50 of module CallReturn2: 0\n" + 
				"  line 168, col 9 to line 170, col 26 of module CallReturn2: 1\n" + 
				"  line 171, col 9 to line 171, col 18 of module CallReturn2: 1\n" + 
				"  line 172, col 19 to line 172, col 60 of module CallReturn2: 0\n" + 
				"  line 175, col 12 to line 175, col 18 of module CallReturn2: 1\n" + 
				"  line 176, col 12 to line 181, col 29 of module CallReturn2: 1\n" + 
				"  line 182, col 9 to line 182, col 17 of module CallReturn2: 1\n" + 
				"  line 183, col 9 to line 183, col 19 of module CallReturn2: 1\n" + 
				"  line 184, col 9 to line 184, col 19 of module CallReturn2: 1\n" + 
				"  line 185, col 19 to line 185, col 48 of module CallReturn2: 0\n" + 
				"  line 189, col 41 to line 189, col 44 of module CallReturn2: 0\n" + 
				"  line 80, col 10 to line 80, col 29 of module CallReturn2: 2\n" + 
				"  line 81, col 10 to line 81, col 29 of module CallReturn2: 2\n" + 
				"  line 82, col 10 to line 82, col 27 of module CallReturn2: 2\n" + 
				"  line 83, col 10 to line 83, col 27 of module CallReturn2: 2\n" + 
				"  line 84, col 10 to line 84, col 29 of module CallReturn2: 2\n" + 
				"  line 85, col 20 to line 85, col 51 of module CallReturn2: 0\n" + 
				"  line 90, col 13 to line 90, col 18 of module CallReturn2: 1\n" + 
				"  line 91, col 13 to line 96, col 36 of module CallReturn2: 1\n" + 
				"  line 97, col 10 to line 97, col 17 of module CallReturn2: 1\n" + 
				"  line 98, col 10 to line 98, col 19 of module CallReturn2: 1\n" + 
				"  line 99, col 10 to line 99, col 19 of module CallReturn2: 1");
	}
}
