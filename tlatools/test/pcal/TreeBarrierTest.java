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

public class TreeBarrierTest extends PCalModelCheckerTestCase {

	public TreeBarrierTest() {
		super("TreeBarrier", "pcal", new String[] {"-wfNext"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "12570", "6 branches of ")); // 6 * 2095 = 12570 
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "5414", "2095", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "106"));

		assertCoverage("  line 100, col 16 to line 100, col 47 of module TreeBarrier: 78\n" +
			"  line 101, col 26 to line 101, col 41 of module TreeBarrier: 0\n" +
			"  line 105, col 16 to line 105, col 63 of module TreeBarrier: 639\n" +
			"  line 106, col 16 to line 106, col 47 of module TreeBarrier: 639\n" +
			"  line 107, col 26 to line 107, col 44 of module TreeBarrier: 0\n" +
			"  line 110, col 16 to line 110, col 69 of module TreeBarrier: 639\n" +
			"  line 111, col 16 to line 111, col 48 of module TreeBarrier: 639\n" +
			"  line 112, col 26 to line 112, col 50 of module TreeBarrier: 0\n" +
			"  line 120, col 70 to line 120, col 73 of module TreeBarrier: 0\n" +
			"  line 52, col 17 to line 52, col 50 of module TreeBarrier: 725\n" +
			"  line 53, col 27 to line 53, col 54 of module TreeBarrier: 0\n" +
			"  line 57, col 18 to line 57, col 49 of module TreeBarrier: 725\n" +
			"  line 58, col 28 to line 58, col 55 of module TreeBarrier: 0\n" +
			"  line 62, col 27 to line 62, col 58 of module TreeBarrier: 279\n" +
			"  line 63, col 27 to line 63, col 58 of module TreeBarrier: 446\n" +
			"  line 64, col 26 to line 64, col 53 of module TreeBarrier: 0\n" +
			"  line 68, col 16 to line 68, col 65 of module TreeBarrier: 66\n" +
			"  line 69, col 16 to line 69, col 47 of module TreeBarrier: 66\n" +
			"  line 70, col 26 to line 70, col 44 of module TreeBarrier: 0\n" +
			"  line 74, col 16 to line 74, col 69 of module TreeBarrier: 16\n" +
			"  line 75, col 16 to line 75, col 47 of module TreeBarrier: 16\n" +
			"  line 76, col 26 to line 76, col 44 of module TreeBarrier: 0\n" +
			"  line 79, col 16 to line 79, col 63 of module TreeBarrier: 462\n" +
			"  line 80, col 16 to line 80, col 47 of module TreeBarrier: 462\n" +
			"  line 81, col 26 to line 81, col 44 of module TreeBarrier: 0\n" +
			"  line 85, col 27 to line 85, col 53 of module TreeBarrier: 12\n" +
			"  line 86, col 27 to line 86, col 58 of module TreeBarrier: 12\n" +
			"  line 87, col 27 to line 87, col 58 of module TreeBarrier: 1005\n" +
			"  line 88, col 27 to line 88, col 32 of module TreeBarrier: 1005\n" +
			"  line 89, col 26 to line 89, col 50 of module TreeBarrier: 0\n" +
			"  line 93, col 27 to line 93, col 58 of module TreeBarrier: 78\n" +
			"  line 94, col 27 to line 94, col 58 of module TreeBarrier: 243\n" +
			"  line 95, col 26 to line 95, col 53 of module TreeBarrier: 0\n" +
			"  line 98, col 16 to line 98, col 66 of module TreeBarrier: 78\n" +
			"  line 99, col 16 to line 99, col 52 of module TreeBarrier: 78");
	}
}
/*
C:\lamport\tla\pluscal>java -mx1000m -cp "c:/lamport/tla/newtools/tla2-inria-workspace/tla2-inria/tlatools/class" tlc2.TLC -cleanup TreeBarrier.tla         
TLC2 Version 2.05 of 18 May 2012
Running in Model-Checking mode.
Parsing file TreeBarrier.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Naturals.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Sequences.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module TreeBarrier
Starting... (2012-08-10 17:39:50)
Implied-temporal checking--satisfiability problem has 6 branches.
Computing initial states...
Finished computing initial states: 1 distinct state generated.
Checking temporal properties for the complete state space...
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 3.8E-13
  based on the actual fingerprints:  val = 6.4E-14
5414 states generated, 2095 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 106.
Finished. (2012-08-10 17:39:53)
*/