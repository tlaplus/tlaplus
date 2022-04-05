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

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.eclipse.lsp4j.debug.EvaluateResponse;
import org.eclipse.lsp4j.debug.Variable;
import org.junit.Test;

import tlc2.debug.TLCStateStackFrame.DebuggerValue;
import tlc2.output.EC;
import tlc2.value.impl.BoolValue;

public class Debug02Test extends TLCDebuggerTestCase {

	private static final String FOLDER = "debug";
	private static final String RM = "Debug02";

	public Debug02Test() {
		super(RM, FOLDER, new String[] { "-config", "Debug02.tla" }, EC.ExitStatus.SUCCESS);
	}

	@Test
	public void testSpec() throws Exception {

		// xx in Init
		EvaluateResponse var = debugger.evaluate(RM, "x", 6, 9, 6, 9);
		assertEquals(null, var.getType());
		assertEquals(DebuggerValue.NOT_EVALUATED, var.getResult());
		// xx in Next
		var = debugger.evaluate(RM, "x", 7, 14, 7, 14);
		assertEquals(null, var.getType());
		assertEquals(DebuggerValue.NOT_EVALUATED, var.getResult());
		// xx' in Next
		var = debugger.evaluate(RM, "x", 7, 9, 7, 9);
		assertEquals(null, var.getType());
		assertEquals("line 7, col 9 to line 7, col 9 of module Debug02", var.getResult());

		// outer-most frame of Init => xx and xx' still null
		debugger.stepIn();
		assertTrue(debugger.stack.peek() instanceof TLCStateStackFrame);
		var = debugger.evaluate(RM, "x", 6, 9, 6, 9);
		assertEquals(null, var.getType());
		assertEquals(DebuggerValue.NOT_EVALUATED, var.getResult());
		var = debugger.evaluate(RM, "x", 7, 14, 7, 14);
		assertEquals(null, var.getType());
		assertEquals(DebuggerValue.NOT_EVALUATED, var.getResult());
		var = debugger.evaluate(RM, "x", 7, 9, 7, 9);
		assertEquals(null, var.getType());
		assertEquals("line 7, col 9 to line 7, col 9 of module Debug02", var.getResult());

		// xx evaluated, xx' not yet
		debugger.stepIn();
		assertTrue(debugger.stack.peek() instanceof TLCStateStackFrame);
		// xx in Init
		var = debugger.evaluate(RM, "x", 6, 9, 6, 9);
		assertEquals(BoolValue.ValTrue.getTypeString(), var.getType());
		assertEquals("TRUE", var.getResult());
		// xx in Next
		var = debugger.evaluate(RM, "x", 7, 14, 7, 14);
		assertEquals(BoolValue.ValTrue.getTypeString(), var.getType());
		assertEquals("TRUE", var.getResult());
		// xx' in Next
		var = debugger.evaluate(RM, "x", 7, 9, 7, 9);
		assertEquals(null, var.getType());
		assertEquals("line 7, col 9 to line 7, col 9 of module Debug02", var.getResult());

		// outer-most frame of Next => xx evaluated, xx' not yet
		debugger.stepIn(2);
		assertTrue(debugger.stack.peek() instanceof TLCActionStackFrame);
		assertFalse(((TLCActionStackFrame) debugger.stack.peek()).state.allAssigned());
		var = debugger.evaluate(RM, "x", 6, 9, 6, 9);
		assertEquals(BoolValue.ValTrue.getTypeString(), var.getType());
		assertEquals("TRUE", var.getResult());
		var = debugger.evaluate(RM, "x", 7, 14, 7, 14);
		assertEquals(BoolValue.ValTrue.getTypeString(), var.getType());
		assertEquals("TRUE", var.getResult());
		var = debugger.evaluate(RM, "x", 7, 9, 7, 10);
		assertEquals(null, var.getType());
		assertEquals(DebuggerValue.NOT_EVALUATED, var.getResult());

		// ... =~xx
		debugger.stepIn();
		assertTrue(debugger.stack.peek() instanceof TLCActionStackFrame);
		assertFalse(((TLCActionStackFrame) debugger.stack.peek()).state.allAssigned());
		var = debugger.evaluate(RM, "x", 6, 9, 6, 9);
		assertEquals(BoolValue.ValTrue.getTypeString(), var.getType());
		assertEquals("TRUE", var.getResult());
		var = debugger.evaluate(RM, "x", 7, 14, 7, 14);
		assertEquals(BoolValue.ValTrue.getTypeString(), var.getType());
		assertEquals("TRUE", var.getResult());
		var = debugger.evaluate(RM, "x", 7, 9, 7, 10);
		assertEquals(null, var.getType());
		assertEquals(DebuggerValue.NOT_EVALUATED, var.getResult());

		// xx' =~xx
		debugger.stepIn();
		assertTrue(debugger.stack.peek() instanceof TLCActionStackFrame);
		assertFalse(((TLCActionStackFrame) debugger.stack.peek()).state.allAssigned());
		var = debugger.evaluate(RM, "x", 6, 9, 6, 9);
		assertEquals(BoolValue.ValTrue.getTypeString(), var.getType());
		assertEquals("TRUE", var.getResult());
		var = debugger.evaluate(RM, "x", 7, 14, 7, 14);
		assertEquals(BoolValue.ValTrue.getTypeString(), var.getType());
		assertEquals("TRUE", var.getResult());
		var = debugger.evaluate(RM, "x", 7, 9, 7, 10);
		assertEquals(null, var.getType());
		assertEquals(DebuggerValue.NOT_EVALUATED, var.getResult());

		debugger.stepIn();
		assertTrue(debugger.stack.peek() instanceof TLCActionStackFrame);
		assertTrue(((TLCActionStackFrame) debugger.stack.peek()).state.allAssigned());
		var = debugger.evaluate(RM, "x", 6, 9, 6, 9);
		assertEquals(BoolValue.ValTrue.getTypeString(), var.getType());
		assertEquals("TRUE", var.getResult());
		var = debugger.evaluate(RM, "x", 7, 14, 7, 14);
		assertEquals(BoolValue.ValTrue.getTypeString(), var.getType());
		assertEquals("TRUE", var.getResult());
		var = debugger.evaluate(RM, "x", 7, 9, 7, 10);
		assertEquals(BoolValue.ValTrue.getTypeString(), var.getType());
		assertEquals("FALSE", var.getResult());

		// Assert that constants of a single module spec (a spec without instantiation
		// and variables declared only in one module) gets flattened in the variable view.
		final TLCActionStackFrame f = (TLCActionStackFrame) debugger.stack.peek();
		final Variable[] variables = f.getVariables(f.getConstantsId());
		assertEquals(1, variables.length);
		assertEquals("val", variables[0].getName());
		assertEquals("42", variables[0].getValue());
		assertArrayEquals(variables, f.getConstants());
		
		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}
