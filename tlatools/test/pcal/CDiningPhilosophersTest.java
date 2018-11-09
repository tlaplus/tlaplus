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

public class CDiningPhilosophersTest extends PCalModelCheckerTestCase {

	public CDiningPhilosophersTest() {
		super("CDiningPhilosophers", "pcal", new String[] {"-sf"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "301", "118", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "14"));
		
		assertCoverage("  line 100, col 11 to line 100, col 40 of module CDiningPhilosophers: 22\n" + 
				"  line 101, col 11 to line 101, col 40 of module CDiningPhilosophers: 22\n" + 
				"  line 57, col 16 to line 57, col 46 of module CDiningPhilosophers: 59\n" + 
				"  line 58, col 16 to line 58, col 47 of module CDiningPhilosophers: 59\n" + 
				"  line 62, col 16 to line 62, col 54 of module CDiningPhilosophers: 30\n" + 
				"  line 63, col 16 to line 63, col 46 of module CDiningPhilosophers: 30\n" + 
				"  line 67, col 15 to line 67, col 46 of module CDiningPhilosophers: 30\n" + 
				"  line 68, col 15 to line 68, col 24 of module CDiningPhilosophers: 30\n" + 
				"  line 71, col 16 to line 71, col 46 of module CDiningPhilosophers: 30\n" + 
				"  line 72, col 16 to line 72, col 47 of module CDiningPhilosophers: 30\n" + 
				"  line 75, col 16 to line 75, col 54 of module CDiningPhilosophers: 76\n" + 
				"  line 76, col 16 to line 76, col 47 of module CDiningPhilosophers: 76\n" + 
				"  line 82, col 11 to line 82, col 40 of module CDiningPhilosophers: 23\n" + 
				"  line 83, col 11 to line 83, col 40 of module CDiningPhilosophers: 23\n" + 
				"  line 87, col 11 to line 87, col 38 of module CDiningPhilosophers: 10\n" + 
				"  line 88, col 11 to line 88, col 39 of module CDiningPhilosophers: 10\n" + 
				"  line 92, col 10 to line 92, col 39 of module CDiningPhilosophers: 10\n" + 
				"  line 93, col 10 to line 93, col 19 of module CDiningPhilosophers: 10\n" + 
				"  line 96, col 11 to line 96, col 38 of module CDiningPhilosophers: 10\n" + 
				"  line 97, col 11 to line 97, col 40 of module CDiningPhilosophers: 10");
	}
}
