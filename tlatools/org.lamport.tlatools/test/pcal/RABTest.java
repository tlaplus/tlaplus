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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;

public class RABTest extends PCalModelCheckerTestCase {

	public RABTest() {
		super("RAB", "pcal", EC.ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "4"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "551", "350", "130"));
		assertEquals(7, recorder.getRecordAsInt(EC.TLC_SEARCH_DEPTH));

		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>();
		expectedTrace.add("/\\ myattr = (p0 :> \"A\" @@ p1 :> \"A\")\n" + 
				"/\\ temp = ( p0 :>\n" + 
				"      [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> FALSE, value |-> FALSE] ] @@\n" + 
				"  p1 :>\n" + 
				"      [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> FALSE, value |-> FALSE] ] )\n" + 
				"/\\ calc = [A |-> FALSE, B |-> TRUE]\n" + 
				"/\\ pc = (p0 :> \"Loop\" @@ p1 :> \"Loop\")\n" + 
				"/\\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"  B |-> [valid |-> FALSE, value |-> FALSE] ]");
		expectedTrace.add("/\\ myattr = (p0 :> \"A\" @@ p1 :> \"A\")\n" + 
				"/\\ temp = ( p0 :>\n" + 
				"      [ A |-> [valid |-> TRUE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> FALSE, value |-> FALSE] ] @@\n" + 
				"  p1 :>\n" + 
				"      [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> FALSE, value |-> FALSE] ] )\n" + 
				"/\\ calc = [A |-> FALSE, B |-> TRUE]\n" + 
				"/\\ pc = (p0 :> \"FetchFlags\" @@ p1 :> \"Loop\")\n" + 
				"/\\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"  B |-> [valid |-> FALSE, value |-> FALSE] ]");
		expectedTrace.add("/\\ myattr = (p0 :> \"A\" @@ p1 :> \"A\")\n" + 
				"/\\ temp = ( p0 :>\n" + 
				"      [ A |-> [valid |-> TRUE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> FALSE, value |-> FALSE] ] @@\n" + 
				"  p1 :>\n" + 
				"      [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> FALSE, value |-> FALSE] ] )\n" + 
				"/\\ calc = [A |-> FALSE, B |-> TRUE]\n" + 
				"/\\ pc = (p0 :> \"StoreFlags\" @@ p1 :> \"Loop\")\n" + 
				"/\\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"  B |-> [valid |-> FALSE, value |-> FALSE] ]");
		expectedTrace.add("/\\ myattr = (p0 :> \"A\" @@ p1 :> \"B\")\n" + 
				"/\\ temp = ( p0 :>\n" + 
				"      [ A |-> [valid |-> TRUE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> FALSE, value |-> FALSE] ] @@\n" + 
				"  p1 :>\n" + 
				"      [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> TRUE, value |-> TRUE] ] )\n" + 
				"/\\ calc = [A |-> FALSE, B |-> TRUE]\n" + 
				"/\\ pc = (p0 :> \"StoreFlags\" @@ p1 :> \"FetchFlags\")\n" + 
				"/\\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"  B |-> [valid |-> FALSE, value |-> FALSE] ]");
		expectedTrace.add("/\\ myattr = (p0 :> \"A\" @@ p1 :> \"B\")\n" + 
				"/\\ temp = ( p0 :>\n" + 
				"      [ A |-> [valid |-> TRUE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> FALSE, value |-> FALSE] ] @@\n" + 
				"  p1 :>\n" + 
				"      [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> TRUE, value |-> TRUE] ] )\n" + 
				"/\\ calc = [A |-> FALSE, B |-> TRUE]\n" + 
				"/\\ pc = (p0 :> \"StoreFlags\" @@ p1 :> \"StoreFlags\")\n" + 
				"/\\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"  B |-> [valid |-> FALSE, value |-> FALSE] ]");
		expectedTrace.add("/\\ myattr = (p0 :> \"A\" @@ p1 :> \"B\")\n" + 
				"/\\ temp = ( p0 :>\n" + 
				"      [ A |-> [valid |-> TRUE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> FALSE, value |-> FALSE] ] @@\n" + 
				"  p1 :>\n" + 
				"      [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> TRUE, value |-> TRUE] ] )\n" + 
				"/\\ calc = [A |-> FALSE, B |-> TRUE]\n" + 
				"/\\ pc = (p0 :> \"StoreFlags\" @@ p1 :> \"ReadFlags\")\n" + 
				"/\\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"  B |-> [valid |-> TRUE, value |-> TRUE] ]");
		expectedTrace.add("/\\ myattr = (p0 :> \"A\" @@ p1 :> \"B\")\n" + 
				"/\\ temp = ( p0 :>\n" + 
				"      [ A |-> [valid |-> TRUE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> FALSE, value |-> FALSE] ] @@\n" + 
				"  p1 :>\n" + 
				"      [ A |-> [valid |-> FALSE, value |-> FALSE],\n" + 
				"        B |-> [valid |-> TRUE, value |-> TRUE] ] )\n" + 
				"/\\ calc = [A |-> FALSE, B |-> TRUE]\n" + 
				"/\\ pc = (p0 :> \"ReadFlags\" @@ p1 :> \"ReadFlags\")\n" + 
				"/\\ flags = [ A |-> [valid |-> TRUE, value |-> FALSE],\n" + 
				"  B |-> [valid |-> FALSE, value |-> FALSE] ]");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

		assertZeroUncovered();
	}
}
/*
C:\lamport\tla\pluscal>java -mx1000m -cp "c:/lamport/tla/newtools/tla2-inria-workspace/tla2-inria/tlatools/class" tlc2.TLC -cleanup RAB.tla         
TLC2 Version 2.05 of 18 May 2012
Running in Model-Checking mode.
Parsing file RAB.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Naturals.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\Sequences.tla
Parsing file C:\lamport\tla\newtools\tla2-inria-workspace\tla2-inria\tlatools\class\tla2sany\StandardModules\TLC.tla
Semantic processing of module Naturals
Semantic processing of module Sequences
Semantic processing of module TLC
Semantic processing of module RAB
Starting... (2012-08-10 17:38:30)
Computing initial states...
Finished computing initial states: 4 distinct states generated.
Error: Invariant Consistency is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ myattr = (p0 :> "A" @@ p1 :> "A")
/\ temp = ( p0 :>
      [ A |-> [valid |-> FALSE, value |-> FALSE],
        B |-> [valid |-> FALSE, value |-> FALSE] ] @@
  p1 :>
      [ A |-> [valid |-> FALSE, value |-> FALSE],
        B |-> [valid |-> FALSE, value |-> FALSE] ] )
/\ calc = [A |-> FALSE, B |-> TRUE]
/\ pc = (p0 :> "Loop" @@ p1 :> "Loop")
/\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],
  B |-> [valid |-> FALSE, value |-> FALSE] ]

State 2: <Action line 163, col 15 to line 175, col 44 of module RAB>
/\ myattr = (p0 :> "A" @@ p1 :> "A")
/\ temp = ( p0 :>
      [ A |-> [valid |-> TRUE, value |-> FALSE],
        B |-> [valid |-> FALSE, value |-> FALSE] ] @@
  p1 :>
      [ A |-> [valid |-> FALSE, value |-> FALSE],
        B |-> [valid |-> FALSE, value |-> FALSE] ] )
/\ calc = [A |-> FALSE, B |-> TRUE]
/\ pc = (p0 :> "FetchFlags" @@ p1 :> "Loop")
/\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],
  B |-> [valid |-> FALSE, value |-> FALSE] ]

State 3: <Action line 182, col 21 to line 185, col 58 of module RAB>
/\ myattr = (p0 :> "A" @@ p1 :> "A")
/\ temp = ( p0 :>
      [ A |-> [valid |-> TRUE, value |-> FALSE],
        B |-> [valid |-> FALSE, value |-> FALSE] ] @@
  p1 :>
      [ A |-> [valid |-> FALSE, value |-> FALSE],
        B |-> [valid |-> FALSE, value |-> FALSE] ] )
/\ calc = [A |-> FALSE, B |-> TRUE]
/\ pc = (p0 :> "StoreFlags" @@ p1 :> "Loop")
/\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],
  B |-> [valid |-> FALSE, value |-> FALSE] ]

State 4: <Action line 163, col 15 to line 175, col 44 of module RAB>
/\ myattr = (p0 :> "A" @@ p1 :> "B")
/\ temp = ( p0 :>
      [ A |-> [valid |-> TRUE, value |-> FALSE],
        B |-> [valid |-> FALSE, value |-> FALSE] ] @@
  p1 :>
      [ A |-> [valid |-> FALSE, value |-> FALSE],
        B |-> [valid |-> TRUE, value |-> TRUE] ] )
/\ calc = [A |-> FALSE, B |-> TRUE]
/\ pc = (p0 :> "StoreFlags" @@ p1 :> "FetchFlags")
/\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],
  B |-> [valid |-> FALSE, value |-> FALSE] ]

State 5: <Action line 182, col 21 to line 185, col 58 of module RAB>
/\ myattr = (p0 :> "A" @@ p1 :> "B")
/\ temp = ( p0 :>
      [ A |-> [valid |-> TRUE, value |-> FALSE],
        B |-> [valid |-> FALSE, value |-> FALSE] ] @@
  p1 :>
      [ A |-> [valid |-> FALSE, value |-> FALSE],
        B |-> [valid |-> TRUE, value |-> TRUE] ] )
/\ calc = [A |-> FALSE, B |-> TRUE]
/\ pc = (p0 :> "StoreFlags" @@ p1 :> "StoreFlags")
/\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],
  B |-> [valid |-> FALSE, value |-> FALSE] ]

State 6: <Action line 187, col 21 to line 190, col 57 of module RAB>
/\ myattr = (p0 :> "A" @@ p1 :> "B")
/\ temp = ( p0 :>
      [ A |-> [valid |-> TRUE, value |-> FALSE],
        B |-> [valid |-> FALSE, value |-> FALSE] ] @@
  p1 :>
      [ A |-> [valid |-> FALSE, value |-> FALSE],
        B |-> [valid |-> TRUE, value |-> TRUE] ] )
/\ calc = [A |-> FALSE, B |-> TRUE]
/\ pc = (p0 :> "StoreFlags" @@ p1 :> "ReadFlags")
/\ flags = [ A |-> [valid |-> FALSE, value |-> FALSE],
  B |-> [valid |-> TRUE, value |-> TRUE] ]

State 7: <Action line 187, col 21 to line 190, col 57 of module RAB>
/\ myattr = (p0 :> "A" @@ p1 :> "B")
/\ temp = ( p0 :>
      [ A |-> [valid |-> TRUE, value |-> FALSE],
        B |-> [valid |-> FALSE, value |-> FALSE] ] @@
  p1 :>
      [ A |-> [valid |-> FALSE, value |-> FALSE],
        B |-> [valid |-> TRUE, value |-> TRUE] ] )
/\ calc = [A |-> FALSE, B |-> TRUE]
/\ pc = (p0 :> "ReadFlags" @@ p1 :> "ReadFlags")
/\ flags = [ A |-> [valid |-> TRUE, value |-> FALSE],
  B |-> [valid |-> FALSE, value |-> FALSE] ]

551 states generated, 350 distinct states found, 131 states left on queue.
The depth of the complete state graph search is 7.
Finished. (2012-08-10 17:38:30)
*/