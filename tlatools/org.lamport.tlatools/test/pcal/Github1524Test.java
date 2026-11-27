/*******************************************************************************
 * Copyright (c) 2026 Oracle and/or its affiliates. All rights reserved.
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
 ******************************************************************************/
package pcal;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;

/**
 * Reproducer for <a href="https://github.com/tlaplus/tlaplus/issues/1524">GitHub issue #1524</a>.
 * PlusCal renames process {@code First}'s label {@code Shared} to {@code Shared_}
 * because process {@code Second} uses the same label. {@code call NoOp(); goto Shared}
 * stores the unrenamed label in the return frame, so {@code First} never executes
 * {@code x := TRUE}. TLC reports success. It should report that {@code Inv} is violated.
 */
public class Github1524Test extends PCalModelCheckerTestCase {

    public Github1524Test() {
        super("Github1524", "pcal", EC.ExitStatus.VIOLATION_SAFETY);
    }

    @Test
    public void testSpec() {
        assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
        assertTrue(recorder.recordedWithStringValue(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, "Inv"));
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertFalse(recorder.recorded(EC.GENERAL));
        assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "6", "4", "0"));
        assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "4"));

        assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
        final List<String> expectedTrace = new ArrayList<String>(4);
        expectedTrace.add("/\\ stack = <<<<>>, <<>>>>\n"
                + "/\\ x = FALSE\n"
                + "/\\ pc = <<\"Start\", \"Shared\">>");
        expectedTrace.add("/\\ stack = <<<<[pc |-> \"Shared_\", procedure |-> \"NoOp\"]>>, <<>>>>\n"
                + "/\\ x = FALSE\n"
                + "/\\ pc = <<\"Body\", \"Shared\">>");
        expectedTrace.add("/\\ stack = <<<<>>, <<>>>>\n"
                + "/\\ x = FALSE\n"
                + "/\\ pc = <<\"Shared_\", \"Shared\">>");
        expectedTrace.add("/\\ stack = <<<<>>, <<>>>>\n"
                + "/\\ x = TRUE\n"
                + "/\\ pc = <<\"Done\", \"Shared\">>");
        assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

        // Second loops at Shared, so the stuttering-on-termination action is never taken.
        assertUncovered("line 72, col 19 to line 72, col 32 of module Github1524: 0");
    }
}
