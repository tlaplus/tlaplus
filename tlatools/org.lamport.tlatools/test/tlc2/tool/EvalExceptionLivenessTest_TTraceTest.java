/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved.
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
package tlc2.tool;

import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.TTraceModelCheckerTestCase;

public class EvalExceptionLivenessTest_TTraceTest extends TTraceModelCheckerTestCase {

    public EvalExceptionLivenessTest_TTraceTest() {
        super(EvalExceptionLivenessTest.class, EC.ExitStatus.ERROR);
    }	
    
    @Override
	protected boolean doCoverage() {
		return false;
	}

    // See https://github.com/tlaplus/tlaplus/pull/588#issuecomment-821745313.
    @Ignore("TESpec Bug - Monolith")
	@Test
    public void testSpec() {
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "950", "555", "89"));

        // Error: The first argument of <= should be an integer, but instead it is:
        // (-1 :> 0)
		assertTrue(recorder.recordedWithStringValues(EC.GENERAL,
				"TLC threw an unexpected exception.\n"
				+ "This was probably caused by an error in the spec or model.\n"
				+ "See the User Output or TLC Console for clues to what happened.\n"
				+ "The exception was a java.lang.RuntimeException\n"
				+ ": Attempted to check equality of the function <<-2>> with the value:\n"
				+ "-2"));

		final List<String> expectedTrace = new ArrayList<String>(15);
		// 1
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 0 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> FALSE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> TRUE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"ncs\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"ncs\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"M1s\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 2
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 0 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> FALSE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> TRUE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"L1\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"L1\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"M1s\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 3
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 0 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> FALSE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"M1s\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"M1\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"M1s\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 4
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 0 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> TRUE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 2 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"M1s\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"M1\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"L2\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 5
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 0 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> TRUE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"enter\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"M1\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"L2\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 6
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 0 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> FALSE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"wait\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {} @@ -1 :> {})\n"
				+ "/\\ net = ( -2 :> (-2 :> <<>> @@ -1 :> <<[num |-> 1, type |-> \"write\"]>>) @@\n"
				+ "  -1 :> (-2 :> <<>> @@ -1 :> <<>>) )\n"
				+ "/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"pcs\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"L2\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 7
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 1 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> FALSE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"wait\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {} @@ -1 :> {})\n"
				+ "/\\ net = ( -2 :> (-2 :> <<>> @@ -1 :> <<>>) @@\n"
				+ "  -1 :> (-2 :> <<[type |-> \"ack\"]>> @@ -1 :> <<>>) )\n"
				+ "/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"pcs\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"L2\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 8
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 1 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> FALSE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"wait\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {-1} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"pcs\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"L2\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 9
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 1 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> TRUE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"L2\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {-1} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"pcs\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"L2\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 10 (9)
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 1 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> TRUE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 2 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"L2\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {-1} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"pcs\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"L3\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 11 (10)
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 1 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> TRUE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"L3\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {-1} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"pcs\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"L3\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 12
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 1 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> TRUE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 2 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"L3\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {-1} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"pcs\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"scs\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 13
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 1 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> FALSE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> TRUE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"cs\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {-1} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"cs\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"scs\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 14
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 1 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> FALSE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> FALSE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"exit\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {-1} @@ -1 :> {})\n"
				+ "/\\ net = (-2 :> (-2 :> <<>> @@ -1 :> <<>>) @@ -1 :> (-2 :> <<>> @@ -1 :> <<>>))\n"
				+ "/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"ncs\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"scs\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		// 15
		expectedTrace.add("/\\ rnum = (-2 :> (-2 :> 0 @@ -1 :> 0) @@ -1 :> (-2 :> 1 @@ -1 :> 0))\n"
				+ "/\\ msgStop = (-2 :> FALSE @@ -1 :> FALSE)\n"
				+ "/\\ mustRdBar = (<<-2, -1>> :> FALSE @@ <<-1, -2>> :> FALSE)\n"
				+ "/\\ j = (-2 :> 1 @@ -1 :> 1)\n"
				+ "/\\ pc = (-2 :> \"scs\" @@ -1 :> \"ncs\" @@ 12 :> \"a\" @@ 21 :> \"a\")\n"
				+ "/\\ acks = (-2 :> {} @@ -1 :> {})\n"
				+ "/\\ net = ( -2 :> (-2 :> <<>> @@ -1 :> <<[num |-> 0, type |-> \"write\"]>>) @@\n"
				+ "  -1 :> (-2 :> <<>> @@ -1 :> <<>>) )\n"
				+ "/\\ num = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ numBar = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ tempBar = (<<-2, -1>> :> 0 @@ <<-1, -2>> :> 0)\n"
				+ "/\\ pcBar = ( <<-2>> :> \"ncs\" @@\n"
				+ "  <<-1>> :> \"ncs\" @@\n"
				+ "  <<-2, -1>> :> \"scs\" @@\n"
				+ "  <<-1, -2>> :> \"M1s\" @@\n"
				+ "  <<-2, -1, \"wr0\">> :> \"wr0\" @@\n"
				+ "  <<-1, -2, \"wr0\">> :> \"wr0\" )");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
	}
}
