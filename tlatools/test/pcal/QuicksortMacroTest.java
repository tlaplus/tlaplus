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

public class QuicksortMacroTest extends PCalModelCheckerTestCase {

	public QuicksortMacroTest() {
		super("QuicksortMacro", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "27"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "306"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "390", "306", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "13"));

		assertCoverage("  line 100, col 14 to line 100, col 28 of module QuicksortMacro: 44\n" +
			"  line 101, col 11 to line 101, col 20 of module QuicksortMacro: 44\n" +
			"  line 102, col 11 to line 102, col 21 of module QuicksortMacro: 44\n" +
			"  line 103, col 21 to line 103, col 45 of module QuicksortMacro: 0\n" +
			"  line 108, col 15 to line 108, col 27 of module QuicksortMacro: 27\n" +
			"  line 109, col 15 to line 109, col 22 of module QuicksortMacro: 27\n" +
			"  line 110, col 15 to line 115, col 32 of module QuicksortMacro: 27\n" +
			"  line 116, col 12 to line 116, col 21 of module QuicksortMacro: 27\n" +
			"  line 117, col 12 to line 117, col 22 of module QuicksortMacro: 27\n" +
			"  line 118, col 22 to line 118, col 39 of module QuicksortMacro: 0\n" +
			"  line 122, col 41 to line 122, col 44 of module QuicksortMacro: 0\n" +
			"  line 64, col 27 to line 64, col 42 of module QuicksortMacro: 112\n" +
			"  line 70, col 29 to line 70, col 35 of module QuicksortMacro: 112\n" +
			"  line 71, col 22 to line 71, col 32 of module QuicksortMacro: 112\n" +
			"  line 72, col 32 to line 72, col 59 of module QuicksortMacro: 0\n" +
			"  line 73, col 22 to line 73, col 41 of module QuicksortMacro: 64\n" +
			"  line 74, col 22 to line 74, col 47 of module QuicksortMacro: 64\n" +
			"  line 75, col 22 to line 75, col 43 of module QuicksortMacro: 64\n" +
			"  line 76, col 22 to line 76, col 43 of module QuicksortMacro: 64\n" +
			"  line 77, col 22 to line 77, col 41 of module QuicksortMacro: 64\n" +
			"  line 78, col 32 to line 78, col 49 of module QuicksortMacro: 0\n" +
			"  line 81, col 11 to line 81, col 28 of module QuicksortMacro: 48\n" +
			"  line 82, col 11 to line 82, col 21 of module QuicksortMacro: 48\n" +
			"  line 83, col 21 to line 83, col 55 of module QuicksortMacro: 0\n" +
			"  line 86, col 14 to line 86, col 25 of module QuicksortMacro: 48\n" +
			"  line 87, col 14 to line 87, col 23 of module QuicksortMacro: 48\n" +
			"  line 88, col 14 to line 93, col 31 of module QuicksortMacro: 48\n" +
			"  line 94, col 11 to line 94, col 20 of module QuicksortMacro: 48\n" +
			"  line 95, col 11 to line 95, col 21 of module QuicksortMacro: 48\n" +
			"  line 96, col 21 to line 96, col 38 of module QuicksortMacro: 0\n" +
			"  line 99, col 14 to line 99, col 23 of module QuicksortMacro: 44");
	}
}
/*
C:\lamport\tla\pluscal>java -mx1000m -cp "c:/lamport/tla/newtools/tla2-inria-workspace/tla2-inria/tlatools/class" tlc2.TLC -cleanup QuicksortMacro.tla         
TLC2 Version 2.05 of 18 May 2012
Running in Model-Checking mode.
Parsing file QuicksortMacro.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Naturals.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Sequences.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module QuicksortMacro
Starting... (2012-08-10 17:38:27)
Implied-temporal checking--satisfiability problem has 1 branches.
Computing initial states...
Finished computing initial states: 27 distinct states generated.
Checking temporal properties for the complete state space...
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.4E-15
  based on the actual fingerprints:  val = 4.6E-15
390 states generated, 306 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 13.
Finished. (2012-08-10 17:38:28)
*/