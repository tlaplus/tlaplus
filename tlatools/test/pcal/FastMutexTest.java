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

public class FastMutexTest extends PCalModelCheckerTestCase {

	public FastMutexTest() {
		super("FastMutex", "pcal", new String[] {"-wf"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "1415"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2679", "1415", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "60"));

		assertCoverage("  line 102, col 27 to line 102, col 58 of module FastMutex: 160\n" + 
				"  line 103, col 27 to line 103, col 58 of module FastMutex: 126\n" + 
				"  line 104, col 26 to line 104, col 49 of module FastMutex: 0\n" + 
				"  line 107, col 16 to line 107, col 46 of module FastMutex: 160\n" + 
				"  line 108, col 16 to line 108, col 42 of module FastMutex: 160\n" + 
				"  line 109, col 16 to line 109, col 47 of module FastMutex: 160\n" + 
				"  line 110, col 26 to line 110, col 43 of module FastMutex: 0\n" + 
				"  line 115, col 27 to line 115, col 61 of module FastMutex: 90\n" + 
				"  line 116, col 27 to line 116, col 58 of module FastMutex: 90\n" + 
				"  line 117, col 27 to line 117, col 59 of module FastMutex: 60\n" + 
				"  line 118, col 27 to line 118, col 32 of module FastMutex: 60\n" + 
				"  line 119, col 26 to line 119, col 46 of module FastMutex: 0\n" + 
				"  line 124, col 28 to line 124, col 67 of module FastMutex: 24\n" + 
				"  line 126, col 38 to line 126, col 43 of module FastMutex: 24\n" + 
				"  line 127, col 17 to line 127, col 48 of module FastMutex: 48\n" + 
				"  line 128, col 27 to line 128, col 42 of module FastMutex: 0\n" + 
				"  line 133, col 27 to line 133, col 59 of module FastMutex: 174\n" + 
				"  line 134, col 37 to line 134, col 42 of module FastMutex: 174\n" + 
				"  line 135, col 27 to line 135, col 67 of module FastMutex: 36\n" + 
				"  line 136, col 27 to line 136, col 61 of module FastMutex: 36\n" + 
				"  line 137, col 26 to line 137, col 41 of module FastMutex: 0\n" + 
				"  line 140, col 17 to line 140, col 22 of module FastMutex: 174\n" + 
				"  line 141, col 17 to line 141, col 49 of module FastMutex: 174\n" + 
				"  line 142, col 27 to line 142, col 47 of module FastMutex: 0\n" + 
				"  line 145, col 17 to line 145, col 47 of module FastMutex: 258\n" + 
				"  line 146, col 17 to line 146, col 51 of module FastMutex: 258\n" + 
				"  line 147, col 27 to line 147, col 47 of module FastMutex: 0\n" + 
				"  line 65, col 19 to line 65, col 50 of module FastMutex: 238\n" + 
				"  line 66, col 29 to line 66, col 52 of module FastMutex: 0\n" + 
				"  line 69, col 16 to line 69, col 45 of module FastMutex: 238\n" + 
				"  line 70, col 16 to line 70, col 47 of module FastMutex: 238\n" + 
				"  line 71, col 26 to line 71, col 46 of module FastMutex: 0\n" + 
				"  line 74, col 16 to line 74, col 24 of module FastMutex: 238\n" + 
				"  line 75, col 16 to line 75, col 47 of module FastMutex: 238\n" + 
				"  line 76, col 26 to line 76, col 46 of module FastMutex: 0\n" + 
				"  line 80, col 27 to line 80, col 58 of module FastMutex: 80\n" + 
				"  line 81, col 27 to line 81, col 58 of module FastMutex: 152\n" + 
				"  line 82, col 26 to line 82, col 49 of module FastMutex: 0\n" + 
				"  line 85, col 16 to line 85, col 46 of module FastMutex: 164\n" + 
				"  line 86, col 16 to line 86, col 47 of module FastMutex: 164\n" + 
				"  line 87, col 26 to line 87, col 46 of module FastMutex: 0\n" + 
				"  line 92, col 16 to line 92, col 50 of module FastMutex: 84\n" + 
				"  line 93, col 26 to line 93, col 49 of module FastMutex: 0\n" + 
				"  line 96, col 16 to line 96, col 24 of module FastMutex: 198\n" + 
				"  line 97, col 16 to line 97, col 47 of module FastMutex: 198\n" + 
				"  line 98, col 26 to line 98, col 46 of module FastMutex: 0");
	}
}
