/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.BlockJUnit4ClassRunner;
import tlc2.output.EC;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

@RunWith(BlockJUnit4ClassRunner.class)
public class AliasSafetySimuTest extends ModelCheckerTestCase {

    public AliasSafetySimuTest() {
        super("Alias", new String[]{"-config", "Alias.tla", "-simulate", "num=1"}, EC.ExitStatus.VIOLATION_SAFETY);
    }

    @Test
    public void testSpec() {
        assertTrue(recorder.recorded(EC.TLC_FINISHED));

        assertFalse(recorder.recorded(EC.GENERAL));

        // Assert the error trace
        assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
        final List<String> expectedTrace = new ArrayList<>(7);
        // Trace prefix
        expectedTrace.add("""
                /\\ y = FALSE
                /\\ x = 1
                /\\ a = 1
                /\\ b = FALSE
                /\\ anim = "e1: 1 e2: FALSE"
                /\\ te = TRUE
                /\\ TLCGetAction = [ name |-> "UnnamedAction",
                  location |->
                      [ beginLine |-> 26,
                        beginColumn |-> 18,
                        endLine |-> 26,
                        endColumn |-> 26,
                        module |-> "Alias" ],
                  context |-> [] ]
                /\\ lvl = <<1, 1>>""");
        expectedTrace.add("""
                /\\ y = TRUE
                /\\ x = 2
                /\\ a = 1
                /\\ b = FALSE
                /\\ anim = "e1: 2 e2: TRUE"
                /\\ te = TRUE
                /\\ TLCGetAction = [ name |-> "A",
                  location |->
                      [ beginLine |-> 15,
                        beginColumn |-> 1,
                        endLine |-> 17,
                        endColumn |-> 13,
                        module |-> "Alias" ],
                  context |-> [] ]
                /\\ lvl = <<2, 2>>""");
        expectedTrace.add("""
                /\\ y = FALSE
                /\\ x = 3
                /\\ a = 1
                /\\ b = FALSE
                /\\ anim = "e1: 3 e2: FALSE"
                /\\ te = TRUE
                /\\ TLCGetAction = [ name |-> "A",
                  location |->
                      [ beginLine |-> 15,
                        beginColumn |-> 1,
                        endLine |-> 17,
                        endColumn |-> 13,
                        module |-> "Alias" ],
                  context |-> [] ]
                /\\ lvl = <<3, 3>>""");
        expectedTrace.add("""
                /\\ y = TRUE
                /\\ x = 4
                /\\ a = 0
                /\\ b = TRUE
                /\\ anim = "e1: 4 e2: TRUE"
                /\\ te = TRUE
                /\\ TLCGetAction = [ name |-> "A",
                  location |->
                      [ beginLine |-> 15,
                        beginColumn |-> 1,
                        endLine |-> 17,
                        endColumn |-> 13,
                        module |-> "Alias" ],
                  context |-> [] ]
                /\\ lvl = <<4, 4>>""");
        final List<String> expectedActions = new ArrayList<>();
        expectedActions.add("<Initial predicate line 26, col 18 to line 26, col 26 of module Alias>");
        expectedActions.addAll(Collections.nCopies(expectedTrace.size() - 1,
                "<A line 15, col 1 to line 17, col 13 of module Alias>"));
        assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);
    }
}
