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

import org.junit.Test;
import util.ToolIO;

import java.io.IOException;
import java.util.Arrays;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class AssignmentToUndeclaredVariableTest extends PCalTest {
    @Test
    public void procedure() throws IOException {
        var t = new trans();
        // Assignment to constant
        assertEquals(trans.STATUS_EXIT_WITH_ERRORS, t.runMe(new String[]{"-nocfg",
                writeTempFile("AssignmentToUndeclaredVariableTest",
                        """
                                ---- MODULE algo ----
                                CONSTANT c
                                (*
                                --algorithm algo {
                                  variables v, w;
                                    procedure Proc1()\s
                                      {p1 : v := 23;
                                            c := 42 }
                                 {
                                  i: call Proc1();
                                 }
                                }*)
                                ===="""
                )}));

        assertTrue(Arrays.toString(ToolIO.getAllMessages()),
                Arrays.asList(ToolIO.getAllMessages()).contains("""

                        Unrecoverable error:
                         -- Assignment to undeclared variable c
                            at line 8, column 13.
                        """));
    }

    @Test
    public void process() throws IOException {
        // Assignment to constant
        assertEquals(trans.STATUS_EXIT_WITH_ERRORS, new trans().runMe(new String[]{"-nocfg",
                writeTempFile("AssignmentToUndeclaredVariableTest",
                        """
                                ---- MODULE algo ----
                                CONSTANT c
                                (*
                                --algorithm algo {
                                  variables v, w;
                                  process (proc \\in {1,2})
                                    variable loc
                                 {
                                   lbl1: loc := 42;
                                   lbl2: v := 23;
                                   lbl3: w := 174;
                                   lbl4: c := "fail";
                                 }
                                }*)
                                ===="""
                )}));

        assertTrue(Arrays.toString(ToolIO.getAllMessages()),
                Arrays.asList(ToolIO.getAllMessages()).contains("""

                        Unrecoverable error:
                         -- Assignment to undeclared variable c
                            at line 12, column 10.
                        """));
    }

    @Test
    public void multiAssignment() throws IOException {
        // Assignment to constant
        assertEquals(trans.STATUS_EXIT_WITH_ERRORS, new trans().runMe(new String[]{"-nocfg",
                writeTempFile("AssignmentToUndeclaredVariableTest",
                        """
                                ---- MODULE algo ----
                                CONSTANT c
                                (*
                                --algorithm algo {
                                  variables v, w;
                                 {
                                  v := 42 || w := 23;
                                  v := 42 || c := 23;
                                 }
                                }*)
                                ===="""
                )}));

        assertTrue(Arrays.toString(ToolIO.getAllMessages()),
                Arrays.asList(ToolIO.getAllMessages()).contains("""

                        Unrecoverable error:
                         -- Assignment to undeclared variable c
                            at line 8, column 11.
                        """));
    }

    @Test
    public void macro() throws IOException {
        // Assignment to constant
        assertEquals(trans.STATUS_EXIT_WITH_ERRORS, new trans().runMe(new String[]{"-nocfg",
                writeTempFile("AssignmentToUndeclaredVariableTest",
                        """
                                ---- MODULE algo ----
                                CONSTANT c
                                (*
                                --algorithm algo {
                                  variables v;
                                  macro Mac() { v := "pmac";
                                 c := 42; }
                                 {
                                  Mac();
                                 }
                                }*)
                                ===="""
                )}));

        assertTrue(Arrays.toString(ToolIO.getAllMessages()),
                Arrays.asList(ToolIO.getAllMessages()).contains("""

                        Unrecoverable error:
                         -- Assignment to undeclared variable c
                            at line 7, column 2 of macro called at line 9, column 3.
                        """));
    }

    @Test
    public void macroParam() throws IOException {
        // Assignment to constant
        assertEquals(trans.STATUS_EXIT_WITH_ERRORS, new trans().runMe(new String[]{"-nocfg",
                writeTempFile("AssignmentToUndeclaredVariableTest",
                        """
                                ---- MODULE algo ----
                                CONSTANT c
                                (*
                                --algorithm algo {
                                  variables v;
                                  macro Mac2(p) { p := "pmac"}
                                 {
                                  lbl1: Mac2(v);
                                  lbl2: Mac2(c);
                                 }
                                }*)
                                ===="""
                )}));

        assertTrue(Arrays.asList(ToolIO.getAllMessages()).contains("""

                Unrecoverable error:
                 -- Assignment to undeclared variable c
                    at line 6, column 19 of macro called at line 9, column 9.
                """));
    }

    @Test
    public void boundIdentifier() throws IOException {
        // Assignment to bound identifier!
        assertEquals(trans.STATUS_EXIT_WITH_ERRORS, new trans().runMe(new String[]{"-nocfg",
                writeTempFile("AssignmentToUndeclaredVariableTest",
                        """
                                ---- MODULE algo ----
                                CONSTANT c
                                (*
                                --algorithm algo
                                  variables v;
                                begin
                                   with n \\in {1,2,3} do
                                      v := n;
                                      n := 42;
                                   end with;end algorithm
                                 *)
                                ===="""
                )}));

        assertTrue(Arrays.asList(ToolIO.getAllMessages()).contains("""

                Unrecoverable error:
                 -- Assignment to undeclared variable n
                    at line 9, column 7.
                """));
    }

    @Test
    public void constant() throws IOException {
        // Assignment to constant!
        assertEquals(trans.STATUS_EXIT_WITH_ERRORS, new trans().runMe(new String[]{"-nocfg",
                writeTempFile("AssignmentToUndeclaredVariableTest",
                        """
                                ---- MODULE algo ----
                                CONSTANT c
                                (*
                                --algorithm algo
                                  variables v;
                                begin
                                   v := 23;
                                   c := 42;
                                end algorithm
                                 *)
                                ===="""
                )}));

        assertTrue(Arrays.asList(ToolIO.getAllMessages()).contains("""

                Unrecoverable error:
                 -- Assignment to undeclared variable c
                    at line 8, column 4.
                """));
    }
}
