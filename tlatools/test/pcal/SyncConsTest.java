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

public class SyncConsTest extends PCalModelCheckerTestCase {

	public SyncConsTest() {
		super("SyncCons", "pcal");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "2"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "22580", "8754", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "48"));

		assertCoverage("  line 136, col 27 to line 136, col 64 of module SyncCons: 892\n" +
			"  line 137, col 27 to line 137, col 58 of module SyncCons: 892\n" +
			"  line 138, col 37 to line 138, col 42 of module SyncCons: 892\n" +
			"  line 139, col 27 to line 141, col 81 of module SyncCons: 1716\n" +
			"  line 142, col 27 to line 142, col 60 of module SyncCons: 1716\n" +
			"  line 143, col 27 to line 143, col 40 of module SyncCons: 1716\n" +
			"  line 144, col 26 to line 144, col 80 of module SyncCons: 0\n" +
			"  line 149, col 32 to line 154, col 74 of module SyncCons: 4168\n" +
			"  line 155, col 32 to line 155, col 85 of module SyncCons: 4168\n" +
			"  line 156, col 27 to line 156, col 58 of module SyncCons: 4168\n" +
			"  line 157, col 27 to line 157, col 58 of module SyncCons: 1724\n" +
			"  line 158, col 37 to line 158, col 55 of module SyncCons: 0\n" +
			"  line 159, col 26 to line 159, col 80 of module SyncCons: 0\n" +
			"  line 163, col 27 to line 163, col 64 of module SyncCons: 736\n" +
			"  line 164, col 27 to line 164, col 61 of module SyncCons: 736\n" +
			"  line 165, col 27 to line 165, col 58 of module SyncCons: 736\n" +
			"  line 166, col 27 to line 166, col 58 of module SyncCons: 988\n" +
			"  line 167, col 37 to line 167, col 53 of module SyncCons: 0\n" +
			"  line 168, col 26 to line 169, col 36 of module SyncCons: 0\n" +
			"  line 178, col 34 to line 181, col 64 of module SyncCons: 3232\n" +
			"  line 182, col 34 to line 182, col 87 of module SyncCons: 3232\n" +
			"  line 183, col 34 to line 183, col 89 of module SyncCons: 3232\n" +
			"  line 184, col 27 to line 184, col 58 of module SyncCons: 3232\n" +
			"  line 185, col 27 to line 185, col 58 of module SyncCons: 760\n" +
			"  line 186, col 37 to line 186, col 61 of module SyncCons: 0\n" +
			"  line 187, col 26 to line 187, col 74 of module SyncCons: 0\n" +
			"  line 191, col 27 to line 191, col 63 of module SyncCons: 84\n" +
			"  line 192, col 27 to line 193, col 88 of module SyncCons: 676\n" +
			"  line 194, col 16 to line 194, col 47 of module SyncCons: 760\n" +
			"  line 195, col 26 to line 196, col 42 of module SyncCons: 0\n" +
			"  line 199, col 16 to line 199, col 64 of module SyncCons: 1748\n" +
			"  line 200, col 16 to line 200, col 47 of module SyncCons: 1748\n" +
			"  line 201, col 26 to line 202, col 42 of module SyncCons: 0\n" +
			"  line 210, col 25 to line 210, col 42 of module SyncCons: 278\n" +
			"  line 211, col 25 to line 211, col 61 of module SyncCons: 278\n" +
			"  line 212, col 25 to line 212, col 59 of module SyncCons: 248\n" +
			"  line 213, col 25 to line 213, col 38 of module SyncCons: 248\n" +
			"  line 214, col 24 to line 215, col 33 of module SyncCons: 0\n" +
			"  line 222, col 26 to line 222, col 54 of module SyncCons: 1228\n" +
			"  line 223, col 24 to line 223, col 59 of module SyncCons: 1228\n" +
			"  line 224, col 24 to line 224, col 58 of module SyncCons: 4070\n" +
			"  line 225, col 34 to line 225, col 40 of module SyncCons: 4070\n" +
			"  line 226, col 23 to line 227, col 32 of module SyncCons: 0\n" +
			"  line 234, col 70 to line 234, col 73 of module SyncCons: 0");
	}
}
/*
C:\lamport\tla\pluscal>java -mx1000m -cp "c:/lamport/tla/newtools/tla2-inria-workspace/tla2-inria/tlatools/class" tlc2.TLC -cleanup SyncCons.tla         
TLC2 Version 2.05 of 18 May 2012
Running in Model-Checking mode.
Parsing file SyncCons.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Naturals.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\FiniteSets.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\TLC.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Sequences.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module FiniteSets
Semantic processing of module TLC
Semantic processing of module SyncCons
Starting... (2012-08-10 17:39:56)
Computing initial states...
Finished computing initial states: 2 distinct states generated.
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 6.6E-12
  based on the actual fingerprints:  val = 4.4E-12
22580 states generated, 8754 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 48.
Finished. (2012-08-10 17:39:57)
*/