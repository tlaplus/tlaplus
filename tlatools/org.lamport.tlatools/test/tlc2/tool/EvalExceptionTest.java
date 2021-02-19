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

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class EvalExceptionTest extends ModelCheckerTestCase {
    public EvalExceptionTest() {
        super("DistBakery", new String[] { "-config", "DistBakery.tla" }, EC.ExitStatus.ERROR);
    }

    @Override
	protected boolean doCoverage() {
		return false;
	}

	@Test
    public void testSpec() {
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "24", "17", "5"));

        // Error: The first argument of <= should be an integer, but instead it is:
        // (-1 :> 0)
		assertTrue(recorder.recordedWithStringValues(EC.TLC_MODULE_ARGUMENT_ERROR_AN,
				"first", "<=", "integer", "(-1 :> 0)"));

		final List<String> expectedTrace = new ArrayList<String>(6);
		expectedTrace.add("/\\ num = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ rnum = (-2 :> (-1 :> 0) @@ -1 :> (-2 :> 0))\n"
				+ "/\\ net = (-2 :> (-1 :> <<>>) @@ -1 :> (-2 :> <<>>))\n"
				+ "/\\ acks = (-2 :> {} @@ -1 :> {})\n"
				+ "/\\ pc = ( [node |-> -2, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -2, type |-> \"mutex\"] :> \"ncs\" @@\n"
				+ "  [node |-> -1, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -1, type |-> \"mutex\"] :> \"ncs\" )");
		expectedTrace.add("/\\ num = (-2 :> 0 @@ -1 :> 0)\n"
				+ "/\\ rnum = (-2 :> (-1 :> 0) @@ -1 :> (-2 :> 0))\n"
				+ "/\\ net = (-2 :> (-1 :> <<>>) @@ -1 :> (-2 :> <<>>))\n"
				+ "/\\ acks = (-2 :> {} @@ -1 :> {})\n"
				+ "/\\ pc = ( [node |-> -2, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -2, type |-> \"mutex\"] :> \"enter\" @@\n"
				+ "  [node |-> -1, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -1, type |-> \"mutex\"] :> \"ncs\" )");
		expectedTrace.add("/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ rnum = (-2 :> (-1 :> 0) @@ -1 :> (-2 :> 0))\n"
				+ "/\\ net = (-2 :> (-1 :> <<[type |-> \"write\", num |-> 1]>>) @@ -1 :> (-2 :> <<>>))\n"
				+ "/\\ acks = (-2 :> {-2} @@ -1 :> {})\n"
				+ "/\\ pc = ( [node |-> -2, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -2, type |-> \"mutex\"] :> \"e1\" @@\n"
				+ "  [node |-> -1, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -1, type |-> \"mutex\"] :> \"ncs\" )");
		expectedTrace.add("/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ rnum = (-2 :> (-1 :> 0) @@ -1 :> (-2 :> 0))\n"
				+ "/\\ net = (-2 :> (-1 :> <<[type |-> \"write\", num |-> 1]>>) @@ -1 :> (-2 :> <<>>))\n"
				+ "/\\ acks = (-2 :> {-2} @@ -1 :> {})\n"
				+ "/\\ pc = ( [node |-> -2, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -2, type |-> \"mutex\"] :> \"e1\" @@\n"
				+ "  [node |-> -1, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -1, type |-> \"mutex\"] :> \"enter\" )");
		expectedTrace.add("/\\ num = (-2 :> 1 @@ -1 :> 0)\n"
				+ "/\\ rnum = (-2 :> (-1 :> 0) @@ -1 :> (-2 :> 1))\n"
				+ "/\\ net = (-2 :> (-1 :> <<>>) @@ -1 :> (-2 :> <<[type |-> \"ack\"]>>))\n"
				+ "/\\ acks = (-2 :> {-2} @@ -1 :> {})\n"
				+ "/\\ pc = ( [node |-> -2, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -2, type |-> \"mutex\"] :> \"e1\" @@\n"
				+ "  [node |-> -1, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -1, type |-> \"mutex\"] :> \"enter\" )");
		expectedTrace.add("/\\ num = (-2 :> 1 @@ -1 :> (-1 :> 0))\n"
				+ "/\\ rnum = (-2 :> (-1 :> 0) @@ -1 :> (-2 :> 1))\n"
				+ "/\\ net = ( -2 :> (-1 :> <<>>) @@\n"
				+ "  -1 :> (-2 :> <<[type |-> \"ack\"], [type |-> \"write\", num |-> (-1 :> 0)]>>) )\n"
				+ "/\\ acks = (-2 :> {-2} @@ -1 :> {-1})\n"
				+ "/\\ pc = ( [node |-> -2, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -2, type |-> \"mutex\"] :> \"e1\" @@\n"
				+ "  [node |-> -1, type |-> \"msg\"] :> \"a\" @@\n"
				+ "  [node |-> -1, type |-> \"mutex\"] :> \"e1\" )");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

		assertTrue(recorder.recordedWithStringValues(EC.TLC_NESTED_EXPRESSION,
				"0. Line 209, column 5 to line 209, column 32 in DistBakery\n"
				+ "1. Line 209, column 22 to line 209, column 32 in DistBakery\n"
				+ "\n"));
	}
}
