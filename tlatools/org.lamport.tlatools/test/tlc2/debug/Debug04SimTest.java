/*******************************************************************************
 * Copyright (c) 2025 NVIDIA Corp. All rights reserved. 
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
import static org.junit.Assert.assertTrue;

import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;
import org.junit.Test;

import tlc2.debug.GotoStateEvent.GotoStateArgument;
import tlc2.output.EC;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import util.UniqueString;

public class Debug04SimTest extends TLCDebuggerTestCase {

	private static final String FOLDER = "debug";
	private static final String RM = "Debug04";

	public Debug04SimTest() {
		super(RM, FOLDER, new String[] { "-config", "Debug04.tla", "-simulate", "num=2" }, EC.ExitStatus.SUCCESS);
	}

	@Test
	public void testSpec() throws Exception {
		debugger.setSpecBreakpoint();

		// 88888888888888888888888888888 Step In 8888888888888888888888888888 //

		StackFrame[] stackFrames = debugger.continue_();
		assertEquals(1, stackFrames.length);
		assertTLCInitStatesFrame(stackFrames[0], 6, 9, 6, 29, RM, Context.Empty, 3);
		TLCInitStatesStackFrame init = (TLCInitStatesStackFrame) stackFrames[0];
		assertEquals(3, init.getStates().size());

		// Goto the first A state (rely on the fact that states are sorted
		// lexicographically, making A the first state. However, assert it).
		final Variable[] statesVariables = init.getStatesVariables();
		final DebugTLCVariable aState = (DebugTLCVariable) statesVariables[0];
		assertEquals(new StringValue("A"), ((RecordValue) aState.getTLCValue()).values[0]);
		debugger.gotoState(new GotoStateArgument()
				.setVariablesReference(aState.getVariablesReference()))
				.whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
		stackFrames = debugger.stackTrace();
		
		// Construct a trace x=A, x=A, ..., x=A by stepping into.
		for (int i = 0; i < 8; i++) {

			// i is number of states in the trace.
			assertEquals(1, stackFrames.length);
			assertTLCNextStatesFrame(stackFrames[0], 16, 20, 16, 23, RM, Context.Empty, 3);

			final TLCNextStatesStackFrame next = (TLCNextStatesStackFrame) stackFrames[0];

			// Check that the TLC state variable 'x' has the expected value.
			assertEquals(new StringValue("A"), next.getS().getVals().get(UniqueString.of("x")));
			
			stackFrames= debugger.stepIn();
		}

		// Reverse direction: back to the initial state.
		for (int i = 8; i > 0; i--) {

			// i is number of states in the trace.
			assertEquals(1, stackFrames.length);
			assertTLCNextStatesFrame(stackFrames[0], 16, 20, 16, 23, RM, Context.Empty, 3);

			final TLCNextStatesStackFrame next = (TLCNextStatesStackFrame) stackFrames[0];

			// Check that the TLC state variable 'x' has the expected value.
			assertEquals(new StringValue("A"), next.getS().getVals().get(UniqueString.of("x")));

			// Select the predecessor state to continue the simulation back.
			// This also continues_ the debugger.
			stackFrames = debugger.stepOut();
		}

		// 88888888888888888888888888888 Step Over 8888888888888888888888888888 //
		
		// Construct a trace x=A, x=B, ..., x=A (no variable values are identical in
		// consecutive states) by stepping over.
		
		stackFrames = debugger.stepOut();
		assertEquals(1, stackFrames.length);
		assertTLCInitStatesFrame(stackFrames[0], 6, 9, 6, 29, RM, Context.Empty, 3);
		init = (TLCInitStatesStackFrame) stackFrames[0];
		assertEquals(3, init.getStates().size());

		debugger.gotoState(new GotoStateArgument()
				.setVariablesReference(init.getStatesVariables()[0].getVariablesReference()))
				.whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
		stackFrames = debugger.stackTrace();

		assertTrue(stackFrames[0] instanceof TLCStateStackFrame);
		IValue oldVal = null;
		
		for (int i = 0; i < 8; i++) {

			// i is number of states in the trace.
			assertEquals(1, stackFrames.length);
			assertTLCNextStatesFrame(stackFrames[0], 16, 20, 16, 23, RM, Context.Empty, 3);

			final TLCNextStatesStackFrame next = (TLCNextStatesStackFrame) stackFrames[0];

			// Check that the TLC state variable 'x' has the expected value.
			assertNotEquals(oldVal, next.getS().getVals().get(UniqueString.of("x")));
			oldVal = ((TLCStateStackFrame) stackFrames[0]).getS().getVals().get(UniqueString.of("x"));
			
			stackFrames = debugger.next();
		}
		
		// Back to the initial states
		stackFrames = debugger.stepOut(8);

		// 8888888888888888888888888 Action-Level Breakpoint Condition 888888888888888888888 //
	
		debugger.setSpecBreakpoint("x = \"A\" /\\ x' = \"B\"");
		stackFrames = debugger.continue_();
		assertTLCNextStatesFrame(stackFrames[0], 16, 20, 16, 23, RM, Context.Empty, 3);
		final TLCNextStatesStackFrame next = (TLCNextStatesStackFrame) stackFrames[0];

		// Check that the TLC state variable 'x' has the expected value.
		assertEquals(new StringValue("A"), next.getS().getVals().get(UniqueString.of("x")));
		assertTrue(next.getSuccessors().stream()
				.anyMatch(s -> new StringValue("B").equals(s.getVals().get(UniqueString.of("x")))));

		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}
