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

public class Quicksort2ProcsTest extends PCalModelCheckerTestCase {

	public Quicksort2ProcsTest() {
		super("Quicksort2Procs", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "27"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "361"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "445", "361", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "15"));

		assertCoverage("  line 104, col 25 to line 104, col 33 of module Quicksort2Procs: 27\n" +
			"  line 105, col 25 to line 105, col 33 of module Quicksort2Procs: 27\n" +
			"  line 106, col 25 to line 110, col 42 of module Quicksort2Procs: 27\n" +
			"  line 111, col 22 to line 111, col 32 of module Quicksort2Procs: 27\n" +
			"  line 112, col 32 to line 112, col 52 of module Quicksort2Procs: 0\n" +
			"  line 113, col 22 to line 113, col 41 of module Quicksort2Procs: 40\n" +
			"  line 114, col 22 to line 114, col 47 of module Quicksort2Procs: 40\n" +
			"  line 115, col 22 to line 115, col 43 of module Quicksort2Procs: 40\n" +
			"  line 116, col 22 to line 116, col 43 of module Quicksort2Procs: 40\n" +
			"  line 117, col 22 to line 117, col 41 of module Quicksort2Procs: 40\n" +
			"  line 118, col 32 to line 118, col 43 of module Quicksort2Procs: 0\n" +
			"  line 119, col 21 to line 119, col 58 of module Quicksort2Procs: 0\n" +
			"  line 122, col 11 to line 122, col 28 of module Quicksort2Procs: 28\n" +
			"  line 123, col 11 to line 123, col 21 of module Quicksort2Procs: 28\n" +
			"  line 124, col 21 to line 125, col 32 of module Quicksort2Procs: 0\n" +
			"  line 128, col 14 to line 128, col 26 of module Quicksort2Procs: 28\n" +
			"  line 129, col 14 to line 129, col 24 of module Quicksort2Procs: 28\n" +
			"  line 130, col 14 to line 135, col 31 of module Quicksort2Procs: 28\n" +
			"  line 136, col 11 to line 136, col 22 of module Quicksort2Procs: 28\n" +
			"  line 137, col 11 to line 137, col 22 of module Quicksort2Procs: 28\n" +
			"  line 138, col 21 to line 138, col 63 of module Quicksort2Procs: 0\n" +
			"  line 141, col 14 to line 141, col 39 of module Quicksort2Procs: 24\n" +
			"  line 142, col 14 to line 142, col 24 of module Quicksort2Procs: 24\n" +
			"  line 143, col 14 to line 143, col 29 of module Quicksort2Procs: 24\n" +
			"  line 144, col 14 to line 149, col 37 of module Quicksort2Procs: 24\n" +
			"  line 150, col 11 to line 150, col 22 of module Quicksort2Procs: 24\n" +
			"  line 151, col 11 to line 151, col 22 of module Quicksort2Procs: 24\n" +
			"  line 152, col 21 to line 152, col 56 of module Quicksort2Procs: 0\n" +
			"  line 158, col 26 to line 158, col 35 of module Quicksort2Procs: 28\n" +
			"  line 159, col 26 to line 159, col 35 of module Quicksort2Procs: 28\n" +
			"  line 160, col 26 to line 164, col 43 of module Quicksort2Procs: 28\n" +
			"  line 165, col 23 to line 165, col 33 of module Quicksort2Procs: 28\n" +
			"  line 166, col 33 to line 166, col 56 of module Quicksort2Procs: 0\n" +
			"  line 167, col 23 to line 167, col 42 of module Quicksort2Procs: 24\n" +
			"  line 168, col 23 to line 168, col 50 of module Quicksort2Procs: 24\n" +
			"  line 169, col 23 to line 169, col 46 of module Quicksort2Procs: 24\n" +
			"  line 170, col 23 to line 170, col 46 of module Quicksort2Procs: 24\n" +
			"  line 171, col 23 to line 171, col 42 of module Quicksort2Procs: 24\n" +
			"  line 172, col 33 to line 172, col 44 of module Quicksort2Procs: 0\n" +
			"  line 173, col 22 to line 173, col 56 of module Quicksort2Procs: 0\n" +
			"  line 176, col 12 to line 176, col 30 of module Quicksort2Procs: 20\n" +
			"  line 177, col 12 to line 177, col 23 of module Quicksort2Procs: 20\n" +
			"  line 178, col 22 to line 179, col 31 of module Quicksort2Procs: 0\n" +
			"  line 182, col 15 to line 182, col 27 of module Quicksort2Procs: 20\n" +
			"  line 183, col 15 to line 183, col 25 of module Quicksort2Procs: 20\n" +
			"  line 184, col 15 to line 189, col 32 of module Quicksort2Procs: 20\n" +
			"  line 190, col 12 to line 190, col 22 of module Quicksort2Procs: 20\n" +
			"  line 191, col 12 to line 191, col 22 of module Quicksort2Procs: 20\n" +
			"  line 192, col 22 to line 192, col 67 of module Quicksort2Procs: 0\n" +
			"  line 195, col 15 to line 195, col 42 of module Quicksort2Procs: 20\n" +
			"  line 196, col 15 to line 196, col 25 of module Quicksort2Procs: 20\n" +
			"  line 197, col 15 to line 197, col 30 of module Quicksort2Procs: 20\n" +
			"  line 198, col 15 to line 203, col 38 of module Quicksort2Procs: 20\n" +
			"  line 204, col 12 to line 204, col 22 of module Quicksort2Procs: 20\n" +
			"  line 205, col 12 to line 205, col 22 of module Quicksort2Procs: 20\n" +
			"  line 206, col 22 to line 206, col 59 of module Quicksort2Procs: 0\n" +
			"  line 211, col 15 to line 211, col 27 of module Quicksort2Procs: 27\n" +
			"  line 212, col 15 to line 212, col 22 of module Quicksort2Procs: 27\n" +
			"  line 213, col 15 to line 218, col 32 of module Quicksort2Procs: 27\n" +
			"  line 219, col 12 to line 219, col 22 of module Quicksort2Procs: 27\n" +
			"  line 220, col 12 to line 220, col 22 of module Quicksort2Procs: 27\n" +
			"  line 221, col 22 to line 221, col 67 of module Quicksort2Procs: 0\n" +
			"  line 225, col 41 to line 225, col 44 of module Quicksort2Procs: 0\n" +
			"  line 87, col 16 to line 87, col 31 of module Quicksort2Procs: 112\n" +
			"  line 93, col 21 to line 93, col 27 of module Quicksort2Procs: 112\n" +
			"  line 94, col 21 to line 94, col 40 of module Quicksort2Procs: 112\n" +
			"  line 95, col 21 to line 95, col 40 of module Quicksort2Procs: 112\n" +
			"  line 96, col 21 to line 96, col 40 of module Quicksort2Procs: 112\n" +
			"  line 97, col 21 to line 97, col 40 of module Quicksort2Procs: 112\n" +
			"  line 98, col 21 to line 98, col 61 of module Quicksort2Procs: 0");
	}
}
/*
C:\lamport\tla\pluscal>java -mx1000m -cp "c:/lamport/tla/newtools/tla2-inria-workspace/tla2-inria/tlatools/class" tlc2.TLC -cleanup Quicksort2Procs.tla         
TLC2 Version 2.05 of 18 May 2012
Running in Model-Checking mode.
Parsing file Quicksort2Procs.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Naturals.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Sequences.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module Quicksort2Procs
Starting... (2012-08-10 17:38:29)
Implied-temporal checking--satisfiability problem has 1 branches.
Computing initial states...
Finished computing initial states: 27 distinct states generated.
Checking temporal properties for the complete state space...
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.6E-15
  based on the actual fingerprints:  val = 1.1E-14
445 states generated, 361 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 15.
Finished. (2012-08-10 17:38:29)
*/