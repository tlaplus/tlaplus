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
import static org.junit.Assert.assertNotEquals;

import org.eclipse.lsp4j.debug.EvaluateResponse;
import org.junit.Test;

import tlc2.output.EC;
import tlc2.value.impl.TupleValue;

public class EWD998TraceDebuggerTest extends TLCDebuggerTestCase {

	private static final String FOLDER = "EWD998";
	private static final String MDL = "EWD998_TTrace";

	public EWD998TraceDebuggerTest() {
		super(MDL, FOLDER, new String[] { "-config", "EWD998_TTrace.tla", "-noGenerateSpecTE" }, EC.ExitStatus.VIOLATION_LIVENESS);
	}

	@Test
	public void testSpec() throws Exception {
		
		debugger.replaceAllBreakpointsWith(MDL, 67);
		debugger.continue_();
		
		EvaluateResponse var = debugger.evaluate(MDL, "_TETrace", 66, 22, 66, 29);
		assertEquals(TupleValue.EmptyTuple.getTypeString(), var.getType());
		assertNotEquals(0, var.getVariablesReference());
		assertEquals(
				"<<[color |-> (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\" @@ 4 :> \"white\"), pending |-> (0 :> 0 @@ 1 :> 0 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0), active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE @@ 4 :> FALSE), counter |-> (0 :> 0 @@ 1 :> 0 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0), token |-> [color |-> \"black\", pos |-> 0, q |-> 0]], [color |-> (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\" @@ 4 :> \"white\"), pending |-> (0 :> 0 @@ 1 :> 0 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0), active |-> (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> FALSE @@ 4 :> FALSE), counter |-> (0 :> 0 @@ 1 :> 0 @@ 2 :> 0 @@ 3 :> 0 @@ 4 :> 0), token |-> [color |-> \"white\", pos |-> 4, q |-> 0]]>>",
				var.getResult());
		
		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}
