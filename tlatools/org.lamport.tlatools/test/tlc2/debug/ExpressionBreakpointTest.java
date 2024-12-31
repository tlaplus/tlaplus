/*******************************************************************************
 * Copyright (c) 2024 Linux Foundation. All rights reserved.
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

package tlc2.debug;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.SourceBreakpoint;
import org.junit.Test;
import org.junit.Assert;

import tlc2.output.EC;
import tlc2.tool.EvalControl;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.LazyValue;
import util.UniqueString;

public class ExpressionBreakpointTest extends TLCDebuggerTestCase {

	private static final String FOLDER = "debug";
	private static final String RM = "ExpressionBreakpointTest";

	public ExpressionBreakpointTest() {
		super(RM, FOLDER, new String[] { "-config", RM + ".tla" }, EC.ExitStatus.SUCCESS);
	}
	
	@Test
	public void testSpec() throws Exception {
		// Set breakpoint
		SourceBreakpoint bp = createBreakpointInfo(8, 5, 1, "(i + l + k) > j");
		SetBreakpointsArguments sba = createBreakpointArgument(RM, bp);
		debugger.setBreakpoints(sba);

		// Break at init
		debugger.continue_();
		
		// Break at bp
		final TLCStateStackFrame current = (TLCStateStackFrame) debugger.continue_()[0];
		Assert.assertEquals(2, ((IntValue) current.getT().getVals().get(UniqueString.of("i"))).val);
		final Map<String, String> allVariables = new HashMap<>();
		allVariables.put("k", "5");
		allVariables.put("l", "4");
		assertTLCStateFrame(current, 8, 8, RM, allVariables);
		
		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}