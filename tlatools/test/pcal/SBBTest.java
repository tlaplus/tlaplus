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

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;

public class SBBTest extends PCalModelCheckerTestCase {

	public SBBTest() {
		super("SBB", "pcal");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "3126", "1617", "328"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "15"));

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

	assertCoverage("  line 100, col 33 to line 100, col 83 of module SBB: 189\n" +
		"  line 101, col 33 to line 101, col 70 of module SBB: 189\n" +
		"  line 102, col 33 to line 102, col 70 of module SBB: 270\n" +
		"  line 103, col 43 to line 103, col 69 of module SBB: 0\n" +
		"  line 104, col 32 to line 104, col 61 of module SBB: 0\n" +
		"  line 107, col 22 to line 107, col 54 of module SBB: 269\n" +
		"  line 108, col 22 to line 108, col 59 of module SBB: 269\n" +
		"  line 109, col 32 to line 109, col 80 of module SBB: 0\n" +
		"  line 112, col 22 to line 112, col 76 of module SBB: 268\n" +
		"  line 113, col 22 to line 113, col 55 of module SBB: 268\n" +
		"  line 114, col 32 to line 114, col 66 of module SBB: 0\n" +
		"  line 118, col 32 to line 118, col 97 of module SBB: 332\n" +
		"  line 119, col 32 to line 119, col 82 of module SBB: 332\n" +
		"  line 121, col 42 to line 121, col 68 of module SBB: 0\n" +
		"  line 122, col 21 to line 122, col 57 of module SBB: 459\n" +
		"  line 123, col 31 to line 123, col 60 of module SBB: 0\n" +
		"  line 126, col 21 to line 126, col 52 of module SBB: 268\n" +
		"  line 127, col 21 to line 127, col 57 of module SBB: 268\n" +
		"  line 128, col 31 to line 128, col 79 of module SBB: 0\n" +
		"  line 131, col 21 to line 131, col 55 of module SBB: 302\n" +
		"  line 132, col 21 to line 132, col 54 of module SBB: 302\n" +
		"  line 133, col 31 to line 133, col 79 of module SBB: 0\n" +
		"  line 89, col 20 to line 89, col 50 of module SBB: 1100\n" +
		"  line 91, col 29 to line 91, col 64 of module SBB: 550\n" +
		"  line 92, col 29 to line 92, col 66 of module SBB: 550\n" +
		"  line 93, col 29 to line 93, col 64 of module SBB: 550\n" +
		"  line 94, col 29 to line 94, col 65 of module SBB: 550\n" +
		"  line 95, col 28 to line 95, col 71 of module SBB: 0\n" +
		"  line 99, col 33 to line 99, col 98 of module SBB: 189");
	}
}
