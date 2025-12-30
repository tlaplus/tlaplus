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
import static org.junit.Assert.assertTrue;

import org.eclipse.lsp4j.debug.StackFrame;
import org.junit.Test;

import tlc2.debug.GotoStateEvent.GotoStateArgument;
import tlc2.output.EC;
import tlc2.util.Context;
import tlc2.value.impl.IntValue;
import util.UniqueString;

public class Debug03SimTest extends TLCDebuggerTestCase {

	private static final String FOLDER = "debug";
	private static final String RM = "Debug03";

	public Debug03SimTest() {
		super(RM, FOLDER, new String[] { "-config", "Debug03.tla", "-simulate", "num=2" }, EC.ExitStatus.SUCCESS);
	}

	@Test
	public void testSpec() throws Exception {
		debugger.setSpecBreakpoint();

		StackFrame[] stackFrames = debugger.continue_();
		assertEquals(1, stackFrames.length);
		assertTLCInitStatesFrame(stackFrames[0], 7, 5, 7, 14, RM, Context.Empty, 2);
		TLCInitStatesStackFrame init = (TLCInitStatesStackFrame) stackFrames[0];
		assertEquals(2, init.getStates().size());

		stackFrames = debugger.continue_();

		// construct a trace x=0 .. x=8 by selecting each successor state in turn.
		for (int i = 0; i < 8; i++) {

			// i is number of states in the trace.
			assertEquals(2 + i, stackFrames.length);
			assertTLCNextStatesFrame(stackFrames[0], 14, 16, 14, 19, RM, Context.Empty, 9);

			final TLCNextStatesStackFrame next = (TLCNextStatesStackFrame) stackFrames[0];

			// Check that the TLC state variable 'x' has the expected value.
			assertEquals(i, ((IntValue) next.getS().getVals().get(UniqueString.of("x"))).val);

			// Assert that the stack frames that have been manually pushed onto the
			// debugger's stack, represent the correct TLC states, i.e., the trace that is
			// constructed.
			for (int j = 0; j < stackFrames.length - 1; j++) {
				final StackFrame frame = stackFrames[stackFrames.length - 1 - j];

				assertTrue(frame instanceof TLCSyntheticStateStackFrame);
				final TLCSyntheticStateStackFrame f = (TLCSyntheticStateStackFrame) frame;

				// Check that the TLC state variable 'x' has the expected value.
				assertEquals(j, ((IntValue) f.getS().getVals().get(UniqueString.of("x"))).val);
			}
			
			// Select the i-th successor state to continue the simulation down that path.
			// This also continues_ the debugger.
			debugger.gotoState(new GotoStateArgument()
					.setVariablesReference(next.getSuccessorVariables()[i].getVariablesReference()))
					.whenComplete((a, b) -> phase.arriveAndAwaitAdvance());

			stackFrames = debugger.stackTrace();
		}

		// Reverse direction: back to the initial state.
		for (int i = 8; i > 0; i--) {

			// i is number of states in the trace.
			assertEquals(2 + i, stackFrames.length);
			assertTLCNextStatesFrame(stackFrames[0], 14, 16, 14, 19, RM, Context.Empty, 9);

			final TLCNextStatesStackFrame next = (TLCNextStatesStackFrame) stackFrames[0];

			// Check that the TLC state variable 'x' has the expected value.
			assertEquals(i, ((IntValue) next.getS().getVals().get(UniqueString.of("x"))).val);
			
			// Assert that the stack frames that have been manually pushed onto the
			// debugger's stack, represent the correct TLC states, i.e., the trace that is
			// deconstructed.
			for (int j = 0; j < stackFrames.length - 1; j++) {
				final StackFrame frame = stackFrames[stackFrames.length - 1 - j];

				assertTrue(frame instanceof TLCSyntheticStateStackFrame);
				final TLCSyntheticStateStackFrame f = (TLCSyntheticStateStackFrame) frame;

				// Check that the TLC state variable 'x' has the expected value.
				assertEquals(j, ((IntValue) f.getS().getVals().get(UniqueString.of("x"))).val);
			}

			// Select the predecessor state to continue the simulation back.
			// This also continues_ the debugger.
			debugger.gotoState(
					new GotoStateArgument().setVariablesReference(next.getTraceVariables()[1].getVariablesReference()))
					.whenComplete((a, b) -> phase.arriveAndAwaitAdvance());

			stackFrames = debugger.stackTrace();
		}

		// Revert (step out of the first TLCNextState...) to the set of initial states
		// (this spec has two initial state).
		stackFrames = debugger.stepOut();
		assertTLCInitStatesFrame(stackFrames[0], 7, 5, 7, 14, RM, Context.Empty, 1);
		init = (TLCInitStatesStackFrame) stackFrames[0];
		assertEquals(2, init.getStates().size());
		
		debugger.gotoState(
				new GotoStateArgument().setVariablesReference(init.getStatesVariables()[1].getVariablesReference()))
				.whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
		stackFrames = debugger.stackTrace();
		assertEquals(2, stackFrames.length);
		assertTLCNextStatesFrame(stackFrames[0], 14, 16, 14, 19, RM, Context.Empty, 9);
		final TLCNextStatesStackFrame next = (TLCNextStatesStackFrame) stackFrames[0];
		// Check that the TLC state variable 'x' has the expected value.
		assertEquals(1, ((IntValue) next.getS().getVals().get(UniqueString.of("x"))).val);

		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}
