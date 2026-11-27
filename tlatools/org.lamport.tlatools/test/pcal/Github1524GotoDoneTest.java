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
 * {@code Done} is the implicit termination label and is not in the symbol
 * table. {@code call NoOp(); goto Done} must translate, run {@code NoOp},
 * and stop at {@code Done}.
 *
 * @see Github1524MissingLabelTest
 */
public class Github1524GotoDoneTest extends PCalModelCheckerTestCase {

    public Github1524GotoDoneTest() {
        super("Github1524GotoDone", "", EC.ExitStatus.VIOLATION_SAFETY);
    }

    @Test
    public void testSpec() {
        assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
        assertTrue(recorder.recordedWithStringValue(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, "Inv"));
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertFalse(recorder.recorded(EC.GENERAL));
        assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "3", "3", "0"));
        assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "3"));

        final List<String> expectedTrace = new ArrayList<String>(3);
        expectedTrace.add("/\\ stack = <<>>\n"
                + "/\\ pc = \"Start\"");
        expectedTrace.add("/\\ stack = <<[pc |-> \"Done\", procedure |-> \"NoOp\"]>>\n"
                + "/\\ pc = \"Body\"");
        expectedTrace.add("/\\ stack = <<>>\n"
                + "/\\ pc = \"Done\"");
        assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
    }
}
