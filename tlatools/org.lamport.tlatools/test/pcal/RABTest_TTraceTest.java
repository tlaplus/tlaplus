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
import tlc2.tool.liveness.TTraceModelCheckerTestCase;

public class RABTest_TTraceTest extends TTraceModelCheckerTestCase {

	public RABTest_TTraceTest() {
		super(RABTest.class, "pcal", EC.ExitStatus.VIOLATION_SAFETY);
	}    

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "7", "7", "0"));
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