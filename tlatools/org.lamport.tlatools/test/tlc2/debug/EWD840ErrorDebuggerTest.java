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
package tlc2.debug;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;
import org.junit.Test;

import tla2sany.semantic.OpDeclNode;
import tlc2.util.Context;

public class EWD840ErrorDebuggerTest extends TLCDebuggerTestCase {

	// MC02 is the spec that extends EWD840 and assigns values to constants for TLC.
	private static final String RM = "EWD840";
	private static final String MDL = "Error02";

	public EWD840ErrorDebuggerTest() {
		super(MDL, RM, new String[] { "-config", "Error02.tla" }, -1); // TODO Why does TLC crash with an exit value of
																		// -1?
	}

	@Test
	public void testSpec() throws Exception {
		// This is just the assume that this test ignores.
		StackFrame[] stackFrames = debugger.stackTrace();
		assertEquals(1, stackFrames.length);

		final OpDeclNode[] vars = getVars();

		// There are no breakpoints to unset, but so what...
		debugger.unsetBreakpoints();
		stackFrames = debugger.continue_();
		// Error occurs after TLC generated the first initial state.
		int i = 7;
		assertEquals(i, stackFrames.length);
		assertTLCStateFrame(stackFrames[--i], 20, 3, 23, 21, RM, Context.Empty, vars);
		assertNull(((TLCStackFrame) stackFrames[i]).exception);
		assertTLCStateFrame(stackFrames[--i], 20, 6, 20, 34, RM, Context.Empty, vars);
		assertNull(((TLCStackFrame) stackFrames[i]).exception);
		assertTLCStateFrame(stackFrames[--i], 21, 6, 21, 31, RM, Context.Empty, vars[0], vars[2], vars[3]);
		assertNull(((TLCStackFrame) stackFrames[i]).exception);
		assertTLCStateFrame(stackFrames[--i], 22, 6, 22, 13, RM, Context.Empty, vars[0], vars[2]);
		assertNull(((TLCStackFrame) stackFrames[i]).exception);
		assertTLCStateFrame(stackFrames[--i], 23, 6, 23, 21, RM, Context.Empty, vars[2]);
		assertNull(((TLCStackFrame) stackFrames[i]).exception);
		assertTLCStateFrame(stackFrames[--i], 14, 13, 14, 22, MDL, Context.Empty);
		assertNull(((TLCStackFrame) stackFrames[i]).exception);
		assertTLCStateFrame(stackFrames[--i], 14, 13, 14, 22, MDL, Context.Empty);

		// Assert the exception variable.
		TLCStackFrame stackFrame = (TLCStackFrame) stackFrames[i];
		assertNotNull(stackFrame.exception);
		Variable[] expVar = stackFrame.getExceptionAsVariable();
		assertEquals(1, expVar.length);

		assertEquals("line 14, col 13 to line 14, col 22 of module Error02", expVar[0].getName());
		assertEquals("Attempted to check equality of integer 42 with non-integer:\n\"abc\"", expVar[0].getValue());
		assertEquals("TLCRuntimeException", expVar[0].getType());

		assertEquals(0, stackFrame.getVariables(expVar[0].getVariablesReference()).length);
	}
}
