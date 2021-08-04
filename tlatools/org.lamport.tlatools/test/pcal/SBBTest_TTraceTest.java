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
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.TTraceModelCheckerTestCase;

public class SBBTest_TTraceTest extends TTraceModelCheckerTestCase {

	public SBBTest_TTraceTest() {
		super(SBBTest.class, "pcal", ExitStatus.VIOLATION_SAFETY);
	}

    @Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "15", "15", "0"));
		assertEquals(15, recorder.getRecordAsInt(EC.TLC_SEARCH_DEPTH));

		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>();
		expectedTrace.add("/\\ availablebuffers = {b1, b2, b3}\n" + 
				"/\\ publishedbuffers = {}\n" + 
				"/\\ sb = [buf |-> b0, owner |-> NoPid]\n" + 
				"/\\ buf = (p0 :> NoBuf @@ p1 :> NoBuf)\n" + 
				"/\\ op = (p0 :> {} @@ p1 :> {})\n" + 
				"/\\ pc = (p0 :> \"Loop\" @@ p1 :> \"Loop\")");
		expectedTrace.add("/\\ availablebuffers = {b1, b2, b3}\n" + 
				"/\\ publishedbuffers = {}\n" + 
				"/\\ sb = [buf |-> b0, owner |-> NoPid]\n" + 
				"/\\ buf = (p0 :> b0 @@ p1 :> NoBuf)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> {})\n" + 
				"/\\ pc = (p0 :> \"Publish1\" @@ p1 :> \"Loop\")");
		expectedTrace.add("/\\ availablebuffers = {b1, b2, b3}\n" + 
				"/\\ publishedbuffers = {}\n" + 
				"/\\ sb = [buf |-> b0, owner |-> NoPid]\n" + 
				"/\\ buf = (p0 :> b0 @@ p1 :> NoBuf)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> {})\n" + 
				"/\\ pc = (p0 :> \"Publish2\" @@ p1 :> \"Loop\")");
		expectedTrace.add("/\\ availablebuffers = {b1, b2, b3}\n" + 
				"/\\ publishedbuffers = {}\n" + 
				"/\\ sb = [buf |-> b0, owner |-> NoPid]\n" + 
				"/\\ buf = (p0 :> b0 @@ p1 :> b0)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Publish2\" @@ p1 :> \"Modify1\")");
		expectedTrace.add("/\\ availablebuffers = {b2, b3}\n" + 
				"/\\ publishedbuffers = {}\n" + 
				"/\\ sb = [buf |-> b0, owner |-> NoPid]\n" + 
				"/\\ buf = (p0 :> b0 @@ p1 :> b1)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Publish2\" @@ p1 :> \"Modify2\")");
		expectedTrace.add("/\\ availablebuffers = {b2, b3}\n" + 
				"/\\ publishedbuffers = {}\n" + 
				"/\\ sb = [buf |-> b0, owner |-> p1]\n" + 
				"/\\ buf = (p0 :> b0 @@ p1 :> b1)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Publish2\" @@ p1 :> \"Modify3\")");
		expectedTrace.add("/\\ availablebuffers = {b2, b3}\n" + 
				"/\\ publishedbuffers = {}\n" + 
				"/\\ sb = [buf |-> b1, owner |-> p1]\n" + 
				"/\\ buf = (p0 :> b0 @@ p1 :> b1)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Publish2\" @@ p1 :> \"Loop\")");
		expectedTrace.add("/\\ availablebuffers = {b2, b3}\n" + 
				"/\\ publishedbuffers = {}\n" + 
				"/\\ sb = [buf |-> b1, owner |-> p1]\n" + 
				"/\\ buf = (p0 :> b0 @@ p1 :> b1)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Publish2\" @@ p1 :> \"Modify1\")");
		expectedTrace.add("/\\ availablebuffers = {b2, b3}\n" + 
				"/\\ publishedbuffers = {}\n" + 
				"/\\ sb = [buf |-> b1, owner |-> p1]\n" + 
				"/\\ buf = (p0 :> b0 @@ p1 :> b1)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Publish2\" @@ p1 :> \"Modify2\")");
		expectedTrace.add("/\\ availablebuffers = {b2, b3}\n" + 
				"/\\ publishedbuffers = {}\n" + 
				"/\\ sb = [buf |-> b1, owner |-> NoPid]\n" + 
				"/\\ buf = (p0 :> b0 @@ p1 :> b1)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Publish3\" @@ p1 :> \"Modify2\")");
		expectedTrace.add("/\\ availablebuffers = {b2, b3}\n" + 
				"/\\ publishedbuffers = {b0}\n" + 
				"/\\ sb = [buf |-> b1, owner |-> NoPid]\n" + 
				"/\\ buf = (p0 :> b0 @@ p1 :> b1)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Loop\" @@ p1 :> \"Modify2\")");
		expectedTrace.add("/\\ availablebuffers = {b2, b3}\n" + 
				"/\\ publishedbuffers = {b0}\n" + 
				"/\\ sb = [buf |-> b1, owner |-> NoPid]\n" + 
				"/\\ buf = (p0 :> b1 @@ p1 :> b1)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Publish1\" @@ p1 :> \"Modify2\")");
		expectedTrace.add("/\\ availablebuffers = {b2, b3}\n" + 
				"/\\ publishedbuffers = {b0}\n" + 
				"/\\ sb = [buf |-> b1, owner |-> NoPid]\n" + 
				"/\\ buf = (p0 :> b1 @@ p1 :> b1)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Publish2\" @@ p1 :> \"Modify2\")");
		expectedTrace.add("/\\ availablebuffers = {b2, b3}\n" + 
				"/\\ publishedbuffers = {b0}\n" + 
				"/\\ sb = [buf |-> b1, owner |-> NoPid]\n" + 
				"/\\ buf = (p0 :> b1 @@ p1 :> b1)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Publish3\" @@ p1 :> \"Modify2\")");
		expectedTrace.add("/\\ availablebuffers = {b2, b3}\n" + 
				"/\\ publishedbuffers = {b0, b1}\n" + 
				"/\\ sb = [buf |-> b1, owner |-> NoPid]\n" + 
				"/\\ buf = (p0 :> b1 @@ p1 :> b1)\n" + 
				"/\\ op = (p0 :> \"Publish\" @@ p1 :> \"Modify\")\n" + 
				"/\\ pc = (p0 :> \"Loop\" @@ p1 :> \"Modify2\")");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

		assertZeroUncovered();
	}
}
