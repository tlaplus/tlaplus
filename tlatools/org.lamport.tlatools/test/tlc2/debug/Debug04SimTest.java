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

import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

import org.eclipse.lsp4j.debug.EvaluateArguments;
import org.eclipse.lsp4j.debug.EvaluateArgumentsContext;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;
import org.junit.Test;

import tlc2.debug.GotoStateEvent.GotoStateArgument;
import tlc2.output.EC;
import tlc2.util.Context;
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

		// Debug Expressions initial frame (no action level)
		EvaluateArguments ea = new EvaluateArguments();
		ea.setFrameId(stackFrames[0].getId());
		ea.setContext(EvaluateArgumentsContext.REPL);
		ea.setExpression("x"); // State-level
		assertTrue(debugger.evaluate(ea).get().getResult().startsWith(// Only prefix bc the name of the on-the-fly
				// generated debug module is not known.
				"In evaluation, the identifier x is either undefined or not an operator."));
		ea.setExpression("x'"); // Action-level
		assertTrue(debugger.evaluate(ea).get().getResult().startsWith(
				"In evaluation, the identifier x is either undefined or not an operator."));

		// Goto the first A state (rely on the fact that states are sorted
		// lexicographically, making A the first state. However, assert it).
		final Variable[] statesVariables = init.getStatesVariables();
		final DebugTLCVariable aState = (DebugTLCVariable) statesVariables[0];
		assertEquals(new StringValue("A"), ((RecordValue) aState.getTLCValue()).values[0]);
		debugger.gotoState(new GotoStateArgument()
				.setVariablesReference(aState.getVariablesReference()))
				.whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
		stackFrames = debugger.stackTrace();

		// idempotence check
		assertArrayEquals(stackFrames, debugger.stackTrace());

		// Construct a trace x=A, x=A, ..., x=A by stepping into.
		for (int i = 0; i < 8; i++) {

			// i is number of states in the trace.
			assertEquals(2 + i, stackFrames.length);
			assertTLCNextStatesFrame(stackFrames[0], 16, 20, 16, 23, RM, Context.Empty, 3);

			final TLCNextStatesStackFrame next = (TLCNextStatesStackFrame) stackFrames[0];
			assertTrue(next.getS().allAssigned());

			// Check that the TLC state variable 'x' has the expected value.
			assertEquals(new StringValue("A"), next.getS().getVals().get(UniqueString.of("x")));

			// Debug Expressions next frame (no action level)
			ea = new EvaluateArguments();
			ea.setFrameId(stackFrames[0].getId());
			ea.setContext(EvaluateArgumentsContext.REPL);
			ea.setExpression("x"); // State-level
			assertEquals("A", debugger.evaluate(ea).get().getResult());
			ea.setExpression("x'"); // Action-level
			assertEquals("A", debugger.evaluate(ea).get().getResult());
			// assert that watch and repl are equivalent.
			ea.setContext("watch");
			ea.setExpression("x"); // State-level
			assertEquals("A", debugger.evaluate(ea).get().getResult());
			ea.setExpression("x'"); // Action-level
			assertEquals("A", debugger.evaluate(ea).get().getResult());
			
			ea.setExpression("TLCGet(\"level\")");
			assertEquals(Integer.toString(i + 1), debugger.evaluate(ea).get().getResult());

			// Assert that the stack frames that have been manually pushed onto the
			// debugger's stack, represent the correct TLC states, i.e., the trace that is
			// constructed.
			for (int j = 0; j < stackFrames.length - 1; j++) {
				final StackFrame frame = stackFrames[stackFrames.length - 1 - j];

				assertTrue(frame instanceof TLCSyntheticStateStackFrame);
				final TLCSyntheticStateStackFrame f = (TLCSyntheticStateStackFrame) frame;
				assertTrue(f.getS().allAssigned());

				// Check that the TLC state variable 'x' has the expected value.
				assertEquals(new StringValue("A"), f.getS().getVals().get(UniqueString.of("x")));
			}

			stackFrames= debugger.stepIn();
		}

		// Reverse direction: back to the initial state.
		for (int i = 8; i > 0; i--) {

			// i is number of states in the trace.
			assertEquals(2 + i, stackFrames.length);
			assertTLCNextStatesFrame(stackFrames[0], 16, 20, 16, 23, RM, Context.Empty, 3);

			final TLCNextStatesStackFrame next = (TLCNextStatesStackFrame) stackFrames[0];
			assertTrue(next.getS().allAssigned());

			// Check that the TLC state variable 'x' has the expected value.
			assertEquals(new StringValue("A"), next.getS().getVals().get(UniqueString.of("x")));

			// Debug Expressions next frame (no action level)
			ea = new EvaluateArguments();
			ea.setFrameId(stackFrames[0].getId());
			ea.setContext(EvaluateArgumentsContext.REPL);
			ea.setExpression("x"); // State-level
			assertEquals("A", debugger.evaluate(ea).get().getResult());
			ea.setExpression("x'"); // Action-level
			assertEquals("A", debugger.evaluate(ea).get().getResult());
			// assert that watch and repl are equivalent.
			ea.setContext("watch");
			assertEquals("A", debugger.evaluate(ea).get().getResult());
			ea.setExpression("x'"); // Action-level
			assertEquals("A", debugger.evaluate(ea).get().getResult());

			ea.setExpression("TLCGet(\"level\")");
			assertEquals(Integer.toString(i + 1), debugger.evaluate(ea).get().getResult());

			// Assert that the stack frames that have been manually pushed onto the
			// debugger's stack, represent the correct TLC states, i.e., the trace that is
			// deconstructed.
			for (int j = 0; j < stackFrames.length - 1; j++) {
				final StackFrame frame = stackFrames[stackFrames.length - 1 - j];

				assertTrue(frame instanceof TLCSyntheticStateStackFrame);
				final TLCSyntheticStateStackFrame f = (TLCSyntheticStateStackFrame) frame;
				assertTrue(f.getS().allAssigned());

				// Check that the TLC state variable 'x' has the expected value.
				assertEquals(new StringValue("A"), f.getS().getVals().get(UniqueString.of("x")));
				
				// Debug Expressions (action level)
				ea = new EvaluateArguments();
				ea.setFrameId(frame.getId());
				ea.setContext(EvaluateArgumentsContext.REPL);
				ea.setExpression("x"); // State-level
				assertEquals("A", debugger.evaluate(ea).get().getResult());
				ea.setExpression("x'"); // Action-level
				assertEquals("A", debugger.evaluate(ea).get().getResult());
			}

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

		// Debug Expressions initial frame (no action level)
		ea = new EvaluateArguments();
		ea.setFrameId(stackFrames[0].getId());
		ea.setContext(EvaluateArgumentsContext.REPL);
		ea.setExpression("x"); // State-level
		assertTrue(debugger.evaluate(ea).get().getResult().startsWith(
				"In evaluation, the identifier x is either undefined or not an operator."));
		ea.setExpression("x'"); // Action-level
		assertTrue(debugger.evaluate(ea).get().getResult().startsWith(
				"In evaluation, the identifier x is either undefined or not an operator."));
		// assert that watch and repl are equivalent.
		ea.setContext("watch");
		ea.setExpression("x"); // State-level
		assertTrue(debugger.evaluate(ea).get().getResult().startsWith(
				"In evaluation, the identifier x is either undefined or not an operator."));
		ea.setExpression("x'"); // Action-level
		assertTrue(debugger.evaluate(ea).get().getResult().startsWith(
				"In evaluation, the identifier x is either undefined or not an operator."));

		ea.setExpression("TLCGet(\"level\")");
		assertEquals(Integer.toString(1), debugger.evaluate(ea).get().getResult());

		debugger.gotoState(new GotoStateArgument()
				.setVariablesReference(init.getStatesVariables()[0].getVariablesReference()))
				.whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
		stackFrames = debugger.stackTrace();
		
		// idempotence check
		assertArrayEquals(stackFrames, debugger.stackTrace());

		assertTrue(stackFrames[0] instanceof TLCStateStackFrame);
		StringValue oldVal = null;
		
		for (int i = 0; i < 8; i++) {

			// i is number of states in the trace.
			assertEquals(2 + i, stackFrames.length);
			assertTLCNextStatesFrame(stackFrames[0], 16, 20, 16, 23, RM, Context.Empty, 3);

			final TLCNextStatesStackFrame next = (TLCNextStatesStackFrame) stackFrames[0];
			assertTrue(next.getS().allAssigned());

			// Check that the TLC state variable 'x' has the expected value.
			assertNotEquals(oldVal, next.getS().getVals().get(UniqueString.of("x")));
			oldVal = (StringValue) ((TLCStateStackFrame) stackFrames[0]).getS().getVals().get(UniqueString.of("x"));
			
			// Debug Expressions next frame (no action level)
			ea = new EvaluateArguments();
			ea.setFrameId(stackFrames[0].getId());
			ea.setContext(EvaluateArgumentsContext.REPL);
			ea.setExpression("x"); // State-level
			assertEquals(oldVal.val.toString(), debugger.evaluate(ea).get().getResult());
			ea.setExpression("x'"); // Action-level
			assertEquals(oldVal.val.toString(), debugger.evaluate(ea).get().getResult());

			// assert that watch and repl are equivalent.
			ea.setContext("watch");
			ea.setExpression("x"); // State-level
			assertEquals(oldVal.val.toString(), debugger.evaluate(ea).get().getResult());
			ea.setExpression("x'"); // Action-level
			assertEquals(oldVal.val.toString(), debugger.evaluate(ea).get().getResult());

			ea.setExpression("TLCGet(\"level\")");
			assertEquals(Integer.toString(i + 1), debugger.evaluate(ea).get().getResult());

			stackFrames = debugger.next();
		}
		
		// Back to the initial states
		stackFrames = debugger.stepOut(8);

		// 8888888888888888888888888 Action-Level Breakpoint Condition 888888888888888888888 //
	
		debugger.setSpecBreakpoint("x = \"A\" /\\ x' = \"B\"");
		stackFrames = debugger.continue_();
		assertTLCNextStatesFrame(stackFrames[0], 16, 20, 16, 23, RM, Context.Empty, 3);
		final TLCNextStatesStackFrame next = (TLCNextStatesStackFrame) stackFrames[0];
		assertTrue(next.getS().allAssigned());

		// Check that the TLC state variable 'x' has the expected value.
		assertEquals(new StringValue("A"), next.getS().getVals().get(UniqueString.of("x")));
		assertTrue(next.getSuccessors().stream()
				.anyMatch(s -> new StringValue("B").equals(s.getVals().get(UniqueString.of("x")))));

		// 88888888888888888 ENABLED Next = FALSE with condition 88888888888888 //
		debugger.setSpecBreakpoint("~ENABLED Next");
		stackFrames = debugger.continue_();
		assertTLCNextStatesFrame(stackFrames[0], 16, 20, 16, 23, RM, Context.Empty, 0);
		
		// 88888888888888888 ENABLED Next = FALSE with no condition 88888888888888 //
		debugger.unsetBreakpoints();
		debugger.setSpecBreakpoint();
		// "manually" hit continue until we reach ~ENABLED Next. Compare Debug04.tla
		// where level is set to 50 (+1 for the init state).
		stackFrames = debugger.continue_(51);
		assertTLCNextStatesFrame(stackFrames[0], 16, 20, 16, 23, RM, Context.Empty, 0);

		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}