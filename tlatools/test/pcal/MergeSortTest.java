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

public class MergeSortTest extends PCalModelCheckerTestCase {

	public MergeSortTest() {
		super("MergeSort", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "6"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "80", ""));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "86", "80", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "18"));
		assertCoverage("  line 104, col 21 to line 104, col 41 of module MergeSort: 4\n" +
				"  line 105, col 21 to line 105, col 30 of module MergeSort: 4\n" +
				"  line 106, col 21 to line 106, col 30 of module MergeSort: 10\n" +
				"  line 107, col 21 to line 107, col 26 of module MergeSort: 10\n" +
				"  line 108, col 20 to line 108, col 51 of module MergeSort: 0\n" +
				"  line 111, col 13 to line 111, col 18 of module MergeSort: 4\n" +
				"  line 112, col 13 to line 112, col 18 of module MergeSort: 4\n" +
				"  line 113, col 13 to line 121, col 30 of module MergeSort: 4\n" +
				"  line 122, col 10 to line 122, col 30 of module MergeSort: 4\n" +
				"  line 123, col 10 to line 123, col 30 of module MergeSort: 4\n" +
				"  line 124, col 10 to line 124, col 30 of module MergeSort: 4\n" +
				"  line 125, col 10 to line 125, col 30 of module MergeSort: 4\n" +
				"  line 126, col 10 to line 126, col 19 of module MergeSort: 4\n" +
				"  line 127, col 20 to line 127, col 29 of module MergeSort: 0\n" +
				"  line 130, col 13 to line 130, col 20 of module MergeSort: 4\n" +
				"  line 131, col 13 to line 131, col 18 of module MergeSort: 4\n" +
				"  line 132, col 13 to line 140, col 30 of module MergeSort: 4\n" +
				"  line 141, col 10 to line 141, col 30 of module MergeSort: 4\n" +
				"  line 142, col 10 to line 142, col 30 of module MergeSort: 4\n" +
				"  line 143, col 10 to line 143, col 30 of module MergeSort: 4\n" +
				"  line 144, col 10 to line 144, col 30 of module MergeSort: 4\n" +
				"  line 145, col 10 to line 145, col 19 of module MergeSort: 4\n" +
				"  line 146, col 20 to line 146, col 29 of module MergeSort: 0\n" +
				"  line 149, col 10 to line 149, col 15 of module MergeSort: 4\n" +
				"  line 150, col 10 to line 150, col 19 of module MergeSort: 4\n" +
				"  line 151, col 20 to line 151, col 51 of module MergeSort: 0\n" +
				"  line 155, col 21 to line 155, col 47 of module MergeSort: 4\n" +
				"  line 156, col 21 to line 156, col 30 of module MergeSort: 4\n" +
				"  line 157, col 21 to line 157, col 30 of module MergeSort: 4\n" +
				"  line 158, col 21 to line 158, col 26 of module MergeSort: 4\n" +
				"  line 160, col 32 to line 160, col 37 of module MergeSort: 4\n" +
				"  line 162, col 32 to line 162, col 61 of module MergeSort: 0\n" +
				"  line 163, col 21 to line 163, col 30 of module MergeSort: 4\n" +
				"  line 164, col 21 to line 164, col 30 of module MergeSort: 4\n" +
				"  line 165, col 21 to line 165, col 26 of module MergeSort: 4\n" +
				"  line 166, col 20 to line 166, col 45 of module MergeSort: 0\n" +
				"  line 170, col 21 to line 170, col 59 of module MergeSort: 4\n" +
				"  line 171, col 21 to line 171, col 30 of module MergeSort: 4\n" +
				"  line 172, col 21 to line 172, col 30 of module MergeSort: 4\n" +
				"  line 173, col 31 to line 173, col 40 of module MergeSort: 0\n" +
				"  line 175, col 32 to line 175, col 37 of module MergeSort: 4\n" +
				"  line 176, col 32 to line 176, col 37 of module MergeSort: 4\n" +
				"  line 178, col 32 to line 178, col 61 of module MergeSort: 0\n" +
				"  line 179, col 32 to line 179, col 37 of module MergeSort: 0\n" +
				"  line 180, col 21 to line 180, col 26 of module MergeSort: 4\n" +
				"  line 181, col 21 to line 181, col 30 of module MergeSort: 4\n" +
				"  line 182, col 21 to line 182, col 26 of module MergeSort: 4\n" +
				"  line 183, col 20 to line 183, col 42 of module MergeSort: 0\n" +
				"  line 188, col 32 to line 188, col 58 of module MergeSort: 1\n" +
				"  line 189, col 32 to line 189, col 41 of module MergeSort: 1\n" +
				"  line 190, col 32 to line 190, col 37 of module MergeSort: 1\n" +
				"  line 191, col 32 to line 191, col 58 of module MergeSort: 7\n" +
				"  line 192, col 32 to line 192, col 41 of module MergeSort: 7\n" +
				"  line 193, col 32 to line 193, col 37 of module MergeSort: 7\n" +
				"  line 194, col 21 to line 194, col 30 of module MergeSort: 8\n" +
				"  line 195, col 21 to line 195, col 30 of module MergeSort: 8\n" +
				"  line 196, col 21 to line 196, col 30 of module MergeSort: 4\n" +
				"  line 197, col 31 to line 197, col 46 of module MergeSort: 0\n" +
				"  line 198, col 20 to line 198, col 42 of module MergeSort: 0\n" +
				"  line 201, col 10 to line 201, col 29 of module MergeSort: 14\n" +
				"  line 202, col 10 to line 202, col 27 of module MergeSort: 14\n" +
				"  line 203, col 10 to line 203, col 27 of module MergeSort: 14\n" +
				"  line 204, col 10 to line 204, col 27 of module MergeSort: 14\n" +
				"  line 205, col 10 to line 205, col 27 of module MergeSort: 14\n" +
				"  line 206, col 10 to line 206, col 27 of module MergeSort: 14\n" +
				"  line 207, col 10 to line 207, col 27 of module MergeSort: 14\n" +
				"  line 208, col 10 to line 208, col 29 of module MergeSort: 14\n" +
				"  line 209, col 20 to line 209, col 29 of module MergeSort: 0\n" +
				"  line 214, col 15 to line 214, col 20 of module MergeSort: 6\n" +
				"  line 215, col 15 to line 215, col 25 of module MergeSort: 6\n" +
				"  line 216, col 15 to line 224, col 32 of module MergeSort: 6\n" +
				"  line 225, col 12 to line 225, col 32 of module MergeSort: 6\n" +
				"  line 226, col 12 to line 226, col 32 of module MergeSort: 6\n" +
				"  line 227, col 12 to line 227, col 32 of module MergeSort: 6\n" +
				"  line 228, col 12 to line 228, col 32 of module MergeSort: 6\n" +
				"  line 229, col 12 to line 229, col 21 of module MergeSort: 6\n" +
				"  line 230, col 22 to line 230, col 31 of module MergeSort: 0\n" +
				"  line 234, col 41 to line 234, col 44 of module MergeSort: 0");
	}
}
/*
C:\lamport\tla\pluscal>java -mx1000m -cp "c:/lamport/tla/newtools/tla2-inria-workspace/tla2-inria/tlatools/class" tlc2.TLC -cleanup MergeSort.tla         
TLC2 Version 2.05 of 18 May 2012
Running in Model-Checking mode.
Parsing file MergeSort.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Naturals.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Sequences.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\TLC.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module TLC
Semantic processing of module MergeSort
Starting... (2012-08-10 17:38:17)
Implied-temporal checking--satisfiability problem has 1 branches.
<<"Testing Mergesort on all arrays of length <= ", 2>>  TRUE
Computing initial states...
Finished computing initial states: 6 distinct states generated.
Checking temporal properties for the complete state space...
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 2.6E-17
  based on the actual fingerprints:  val = 1.6E-16
86 states generated, 80 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 18.
Finished. (2012-08-10 17:38:17)
*/
