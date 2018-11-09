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

public class QuicksortTest extends PCalModelCheckerTestCase {

	public QuicksortTest() {
		super("Quicksort", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "27"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "933"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "1017", "933", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "16"));

		assertCoverage("  line 100, col 22 to line 100, col 43 of module Quicksort: 177\n" +
			"  line 101, col 22 to line 101, col 43 of module Quicksort: 177\n" +
			"  line 102, col 22 to line 102, col 41 of module Quicksort: 177\n" +
			"  line 103, col 32 to line 103, col 43 of module Quicksort: 0\n" +
			"  line 104, col 21 to line 104, col 45 of module Quicksort: 0\n" +
			"  line 107, col 11 to line 107, col 28 of module Quicksort: 138\n" +
			"  line 108, col 11 to line 108, col 21 of module Quicksort: 138\n" +
			"  line 109, col 21 to line 109, col 70 of module Quicksort: 0\n" +
			"  line 112, col 14 to line 112, col 25 of module Quicksort: 138\n" +
			"  line 113, col 14 to line 113, col 23 of module Quicksort: 138\n" +
			"  line 114, col 14 to line 119, col 31 of module Quicksort: 138\n" +
			"  line 120, col 11 to line 120, col 35 of module Quicksort: 138\n" +
			"  line 121, col 11 to line 121, col 21 of module Quicksort: 138\n" +
			"  line 122, col 21 to line 122, col 53 of module Quicksort: 0\n" +
			"  line 125, col 14 to line 125, col 23 of module Quicksort: 123\n" +
			"  line 126, col 14 to line 126, col 28 of module Quicksort: 123\n" +
			"  line 127, col 11 to line 127, col 35 of module Quicksort: 123\n" +
			"  line 128, col 11 to line 128, col 21 of module Quicksort: 123\n" +
			"  line 129, col 21 to line 129, col 60 of module Quicksort: 0\n" +
			"  line 134, col 15 to line 134, col 27 of module Quicksort: 27\n" +
			"  line 135, col 15 to line 135, col 22 of module Quicksort: 27\n" +
			"  line 136, col 15 to line 141, col 32 of module Quicksort: 27\n" +
			"  line 142, col 12 to line 142, col 36 of module Quicksort: 27\n" +
			"  line 143, col 12 to line 143, col 22 of module Quicksort: 27\n" +
			"  line 144, col 22 to line 144, col 54 of module Quicksort: 0\n" +
			"  line 151, col 12 to line 151, col 23 of module Quicksort: 54\n" +
			"  line 152, col 22 to line 152, col 78 of module Quicksort: 0\n" +
			"  line 156, col 41 to line 156, col 44 of module Quicksort: 0\n" +
			"  line 72, col 16 to line 72, col 31 of module Quicksort: 168\n" +
			"  line 78, col 21 to line 78, col 27 of module Quicksort: 168\n" +
			"  line 79, col 21 to line 79, col 40 of module Quicksort: 168\n" +
			"  line 80, col 21 to line 80, col 40 of module Quicksort: 168\n" +
			"  line 81, col 21 to line 81, col 40 of module Quicksort: 168\n" +
			"  line 82, col 21 to line 82, col 40 of module Quicksort: 168\n" +
			"  line 83, col 21 to line 83, col 48 of module Quicksort: 0\n" +
			"  line 89, col 25 to line 89, col 33 of module Quicksort: 111\n" +
			"  line 90, col 25 to line 90, col 33 of module Quicksort: 111\n" +
			"  line 91, col 25 to line 95, col 42 of module Quicksort: 111\n" +
			"  line 96, col 22 to line 96, col 32 of module Quicksort: 111\n" +
			"  line 97, col 32 to line 97, col 52 of module Quicksort: 0\n" +
			"  line 98, col 22 to line 98, col 41 of module Quicksort: 177\n" +
			"  line 99, col 22 to line 99, col 47 of module Quicksort: 177");
	}
}
/*
C:\lamport\tla\pluscal>java -mx1000m -cp "c:/lamport/tla/newtools/tla2-inria-workspace/tla2-inria/tlatools/class" tlc2.TLC -cleanup Quicksort.tla         
TLC2 Version 2.05 of 18 May 2012
Running in Model-Checking mode.
Parsing file Quicksort.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Naturals.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Sequences.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\TLC.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module TLC
Semantic processing of module Quicksort
Starting... (2012-08-10 17:38:26)
Implied-temporal checking--satisfiability problem has 1 branches.
Computing initial states...
Finished computing initial states: 27 distinct states generated.
Checking temporal properties for the complete state space...
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 4.2E-15
  based on the actual fingerprints:  val = 2.3E-14
1017 states generated, 933 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 16.
Finished. (2012-08-10 17:38:26)
*/