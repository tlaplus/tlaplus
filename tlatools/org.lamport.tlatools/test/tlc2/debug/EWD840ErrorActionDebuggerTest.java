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

import tlc2.util.Context;

public class EWD840ErrorActionDebuggerTest extends TLCDebuggerTestCase {

	// MC02 is the spec that extends EWD840 and assigns values to constants for TLC.
	private static final String RM = "EWD840";
	private static final String MDL = "Error03";

	public EWD840ErrorActionDebuggerTest() {
		super(MDL, RM, new String[] { "-config", "Error03.tla" }, -1); // TODO Why does TLC crash with an exit value of
																		// -1?
	}

	@Test
	public void testSpec() throws Exception {
		// This is just the assume that this test ignores.
		StackFrame[] stackFrames = debugger.stackTrace();
		assertEquals(1, stackFrames.length);

		// There are no breakpoints to unset, but so what...
		debugger.unsetBreakpoints();
		stackFrames = debugger.continue_();
		// Error occurs after TLC generated the first initial state.
		int i = 17;
		assertEquals(i, stackFrames.length);
		for (int j = i - 1; j > 0 ; j--) {
			assertNull(((TLCStackFrame) stackFrames[j]).exception);
		}
		
		assertTLCActionFrame(stackFrames[0], 13, 69, 13, 77, MDL, (Context) null);

		// Assert the exception variable.
		TLCStackFrame stackFrame = (TLCStackFrame) stackFrames[0];
		assertNotNull(stackFrame.exception);
		Variable[] expVar = stackFrame.getExceptionAsVariable();
		assertEquals(1, expVar.length);

		assertEquals("line 13, col 69 to line 13, col 77 of module Error03", expVar[0].getName());
		assertEquals("Attempted to check equality of integer 0 with non-integer:\n\"abc\"", expVar[0].getValue());
		assertEquals("TLCRuntimeException", expVar[0].getType());

		assertEquals(0, stackFrame.getVariables(expVar[0].getVariablesReference()).length);
	}
}
