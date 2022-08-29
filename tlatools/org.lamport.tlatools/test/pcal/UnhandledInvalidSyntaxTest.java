/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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

import org.junit.Test;
import util.ToolIO;

import java.io.IOException;
import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class UnhandledInvalidSyntaxTest extends PCalTest {

    @Test
    public void test1() throws IOException {
        assertEquals(trans.STATUS_EXIT_WITH_ERRORS, new trans().runMe(new String[]{"-nocfg",
                writeTempFile("MissingSemicolonTest1",
                        """
                                ---- MODULE algo ----
                                (*
                                 --algorithm algo
                                 begin
                                 await;
                                 end algorithm;
                                *)
                                ===="""
                )}));

        assertTrue(Arrays.toString(ToolIO.getAllMessages()),
                Arrays.asList(ToolIO.getAllMessages()).contains("""

                        Unrecoverable error:
                         -- Unknown error at or before
                            line 5, column 2.
                        """));
    }

    @Test
    public void test2() throws IOException {
        // missing semicolon
        assertEquals(trans.STATUS_EXIT_WITH_ERRORS, new trans().runMe(new String[]{"-nocfg",
                writeTempFile("MissingSemicolonTest2",
                        """
                                ---- MODULE algo ----
                                (*
                                 --algorithm algo
                                 begin
                                 if TRUE then
                                 end if;
                                 end algorithm;
                                *)
                                ===="""
                )}));

        assertTrue(Arrays.toString(ToolIO.getAllMessages()),
                Arrays.asList(ToolIO.getAllMessages()).contains("""

                        Unrecoverable error:
                         -- Unknown error at or before
                            line 6, column 8.
                        """));
    }
}