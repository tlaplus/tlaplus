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

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.tool.CommonTestCase;
import util.ToolIO;

/**
 * {@code OnlyB} is a label of process {@code B}. Process {@code A} has no
 * such label, and {@code B} can still take a step, so accepting
 * {@code call NoOp(); goto OnlyB} would leave {@code A} at a {@code pc} for
 * which it has no action.
 *
 * @see Github1524Test
 */
public class Github1524OtherProcessTest extends PCalTest {

    @Test
    public void test() {
        assertUnknownLabel("Github1524OtherProcess.tla", "OnlyB", 9, 5);
    }

    private static void assertUnknownLabel(String module, String label, int line, int column) {
        assertEquals(trans.STATUS_EXIT_WITH_ERRORS,
                trans.runMe(new String[] {"-nocfg", CommonTestCase.BASE_PATH + module}));
        final String[] messages = ToolIO.getAllMessages();
        assertEquals(2, messages.length);
        assertEquals("Parsing completed.", messages[0]);
        assertEquals("Unrecoverable error:\n"
                + " -- goto to non-existent label `" + label
                + "' at line " + line + ", column " + column + ".",
                messages[1].trim());
    }
}
