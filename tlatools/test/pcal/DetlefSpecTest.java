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

public class DetlefSpecTest extends PCalModelCheckerTestCase {

	public DetlefSpecTest() {
		super("DetlefSpec", "pcal", new String[] {"-wf"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "31", "15", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "8"));
		
		assertCoverage("  line 47, col 30 to line 47, col 52 of module DetlefSpec: 4\n" + 
				"  line 48, col 30 to line 48, col 63 of module DetlefSpec: 4\n" + 
				"  line 49, col 30 to line 49, col 53 of module DetlefSpec: 4\n" + 
				"  line 50, col 30 to line 50, col 63 of module DetlefSpec: 4\n" + 
				"  line 51, col 30 to line 51, col 63 of module DetlefSpec: 4\n" + 
				"  line 52, col 30 to line 52, col 43 of module DetlefSpec: 4\n" + 
				"  line 54, col 39 to line 54, col 77 of module DetlefSpec: 3\n" + 
				"  line 55, col 39 to line 55, col 58 of module DetlefSpec: 3\n" + 
				"  line 56, col 39 to line 56, col 83 of module DetlefSpec: 3\n" + 
				"  line 57, col 39 to line 57, col 90 of module DetlefSpec: 3\n" + 
				"  line 58, col 33 to line 58, col 67 of module DetlefSpec: 1\n" + 
				"  line 59, col 33 to line 59, col 46 of module DetlefSpec: 1\n" + 
				"  line 60, col 16 to line 60, col 47 of module DetlefSpec: 19\n" + 
				"  line 63, col 16 to line 63, col 47 of module DetlefSpec: 11\n" + 
				"  line 64, col 16 to line 64, col 47 of module DetlefSpec: 11\n" + 
				"  line 65, col 16 to line 65, col 29 of module DetlefSpec: 11");
	}
}
