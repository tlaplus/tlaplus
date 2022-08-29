/*******************************************************************************
 * Copyright (c) 2022 Microsoft Research. All rights reserved. 
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
package tlc2.debug;

import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.StackFrame;
import org.junit.Test;
import org.junit.experimental.categories.Category;
import tlc2.output.EC;
import tlc2.util.Context;
import util.DebuggerTest;

import static org.junit.Assert.assertEquals;

public class Debug03Test extends TLCDebuggerTestCase {

    private static final String FOLDER = "debug";
    private static final String RM = "Debug03";

    public Debug03Test() {
        super(RM, FOLDER, new String[]{"-config", "Debug03.tla"}, EC.ExitStatus.SUCCESS);
    }

    @Category(DebuggerTest.class)
    @Test
    public void testSpec() throws Exception {

        // Assert that the inline breakpoint on Next shows 9 successor states.
        final SetBreakpointsArguments sba = createBreakpointArgument(RM, 9, 1, 1);
        debugger.setBreakpoints(sba);
        final StackFrame[] stackFrames = debugger.continue_();
        assertEquals(1, stackFrames.length);
        assertTLCSuccessorFrame(stackFrames[0], 9, 1, 11, 18, RM, Context.Empty, 9);

        // Remove all breakpoints and run the spec to completion.
        debugger.unsetBreakpoints();
        debugger.continue_();
    }
}
