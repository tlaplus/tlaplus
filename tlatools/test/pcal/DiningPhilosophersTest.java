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

public class DiningPhilosophersTest extends PCalModelCheckerTestCase {

	public DiningPhilosophersTest() {
		super("DiningPhilosophers", "pcal", new String[] {"-sf"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "118"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "301", "118", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "14"));
		
		assertCoverage("  line 100, col 10 to line 100, col 19 of module DiningPhilosophers: 10\n" + 
				"  line 103, col 11 to line 103, col 38 of module DiningPhilosophers: 10\n" + 
				"  line 104, col 11 to line 104, col 40 of module DiningPhilosophers: 10\n" + 
				"  line 107, col 11 to line 107, col 40 of module DiningPhilosophers: 22\n" + 
				"  line 108, col 11 to line 108, col 40 of module DiningPhilosophers: 22\n" + 
				"  line 64, col 16 to line 64, col 46 of module DiningPhilosophers: 59\n" + 
				"  line 65, col 16 to line 65, col 47 of module DiningPhilosophers: 59\n" + 
				"  line 69, col 16 to line 69, col 54 of module DiningPhilosophers: 30\n" + 
				"  line 70, col 16 to line 70, col 46 of module DiningPhilosophers: 30\n" + 
				"  line 74, col 15 to line 74, col 46 of module DiningPhilosophers: 30\n" + 
				"  line 75, col 15 to line 75, col 24 of module DiningPhilosophers: 30\n" + 
				"  line 78, col 16 to line 78, col 46 of module DiningPhilosophers: 30\n" + 
				"  line 79, col 16 to line 79, col 47 of module DiningPhilosophers: 30\n" + 
				"  line 82, col 16 to line 82, col 54 of module DiningPhilosophers: 76\n" + 
				"  line 83, col 16 to line 83, col 47 of module DiningPhilosophers: 76\n" + 
				"  line 89, col 11 to line 89, col 40 of module DiningPhilosophers: 23\n" + 
				"  line 90, col 11 to line 90, col 40 of module DiningPhilosophers: 23\n" + 
				"  line 94, col 11 to line 94, col 38 of module DiningPhilosophers: 10\n" + 
				"  line 95, col 11 to line 95, col 39 of module DiningPhilosophers: 10\n" + 
				"  line 99, col 10 to line 99, col 39 of module DiningPhilosophers: 10");
	}
}
