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
 * copies or substantial portions of the Softw//are. 
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

import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;
import org.junit.Test;

import tlc2.output.EC;
import tlc2.util.Context;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;

public class EchoDebuggerTest extends TLCDebuggerTestCase {

	private static final String RM = "Echo";
	private static final String MDL = "MCEcho";

	public EchoDebuggerTest() {
		super(MDL, RM, EC.ExitStatus.SUCCESS);
	}

	@Test
	public void testSpec() throws Exception {
/*
	ASSUME /\ initiator \in Node
	       /\ R \in [Node \X Node -> BOOLEAN]
	       \* No edge from a node to itself (self-loops).
	       /\ IsIrreflexive(R, Node)
	       \* Undirected graph (there exists an edge from b 
	       \* to a if there exists an edge from a to b).
	       /\ IsSymmetric(R, Node)
	       \* There exists a spanning tree consisting of *all* nodes.
	       \* (no forest of spanning trees). 
	       /\ IsConnected(R, Node)
 */
		StackFrame[] stackFrames = debugger.stackTrace();
		assertEquals(1, stackFrames.length);
		assertTLCFrame(stackFrames[0], 12, 21, RM);
		// prefix depends on where the tests execute.
		assertTrue(stackFrames[0].getSource().getPath().endsWith("test-model/Echo/Echo.tla"));
		
		TLCStackFrame f = (TLCStackFrame) stackFrames[0];
		Variable[] constants = f.getConstants();
		assertEquals(2, constants.length);
		assertEquals("Echo", constants[0].getName());
		Variable[] nested = f.getVariables(constants[0].getVariablesReference());
		assertEquals(4, nested.length);
		assertEquals("I1", nested[0].getName());
		assertEquals("a", nested[0].getValue());
		assertEquals("N1", nested[1].getName());
		assertEquals("{\"a\", \"b\", \"c\"}", nested[1].getValue());
		assertEquals("ProcSet", nested[2].getName());
		assertEquals("{\"a\", \"b\", \"c\"}", nested[2].getValue());
		assertEquals("R1", nested[3].getName());
		assertEquals("(<<\"a\", \"a\">> :> FALSE @@ <<\"a\", \"b\">> :> TRUE @@ <<\"a\", \"c\">> :> TRUE @@ <<\"b\", \"a\">> :> TRUE @@ <<\"b\", \"b\">> :> FALSE @@ <<\"b\", \"c\">> :> TRUE @@ <<\"c\", \"a\">> :> TRUE @@ <<\"c\", \"b\">> :> TRUE @@ <<\"c\", \"c\">> :> FALSE)", nested[3].getValue());
		
		assertEquals("MCEcho", constants[1].getName());
		nested = f.getVariables(constants[1].getVariablesReference());
		assertEquals(4, nested.length);
		assertEquals("I1", nested[0].getName());
		assertEquals("a", nested[0].getValue());
		assertEquals("N1", nested[1].getName());
		assertEquals("{\"a\", \"b\", \"c\"}", nested[1].getValue());
		assertEquals("R1", nested[2].getName());
		assertEquals("(<<\"a\", \"a\">> :> FALSE @@ <<\"a\", \"b\">> :> TRUE @@ <<\"a\", \"c\">> :> TRUE @@ <<\"b\", \"a\">> :> TRUE @@ <<\"b\", \"b\">> :> FALSE @@ <<\"b\", \"c\">> :> TRUE @@ <<\"c\", \"a\">> :> TRUE @@ <<\"c\", \"b\">> :> TRUE @@ <<\"c\", \"c\">> :> FALSE)", nested[2].getValue());
		assertEquals("R2", nested[3].getName());
		assertEquals("(<<\"a\", \"a\">> :> FALSE @@ <<\"a\", \"b\">> :> FALSE @@ <<\"a\", \"c\">> :> TRUE @@ <<\"b\", \"a\">> :> FALSE @@ <<\"b\", \"b\">> :> FALSE @@ <<\"b\", \"c\">> :> TRUE @@ <<\"c\", \"a\">> :> TRUE @@ <<\"c\", \"b\">> :> TRUE @@ <<\"c\", \"c\">> :> FALSE)", nested[3].getValue());

		// Step into the first conjunct!!! Debugger (VSCode) highlights the full assume
		// before stepping in, because of which a user should understand why step over
		// or out go to Init.
		stackFrames = debugger.stepIn();
		assertEquals(2, stackFrames.length);
		assertTLCFrame(stackFrames[1], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[0], 12, 11, 12, 28, RM); // initiator \in Node

		stackFrames = debugger.stepIn(2);
		assertEquals(4, stackFrames.length);
		assertTLCFrame(stackFrames[3], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[2], 12, 11, 12, 28, RM);
		// filters initiator in initiator \in ...
		assertTLCFrame(stackFrames[1], 12, 11, 12, 19, RM);
		assertTLCFrame(stackFrames[0], 9, 7, 9, 28, MDL);  // CHOOSE n \in N1 : TRUE

		stackFrames = debugger.stepIn();
		assertEquals(5, stackFrames.length);
		assertTLCFrame(stackFrames[4], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[3], 12, 11, 12, 28, RM);
		assertTLCFrame(stackFrames[2], 12, 11, 12, 19, RM);
		assertTLCFrame(stackFrames[1], 9, 7, 9, 28, MDL);
		assertTLCFrame(stackFrames[0], 9, 20, 9, 21, MDL); // N1

		// Cannot step into N1 because SpecProcessor eagerly evaluates N1 as part of
		// constant defs processing. Instead, steps into TRUE.
		// TODO: Why doesn't TLC process I1 as part of constant defs processing?
		stackFrames = debugger.stepIn();
		assertEquals(5, stackFrames.length);
		assertTLCFrame(stackFrames[4], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[3], 12, 11, 12, 28, RM);
		assertTLCFrame(stackFrames[2], 12, 11, 12, 19, RM);
		assertTLCFrame(stackFrames[1], 9, 7, 9, 28, MDL);
		assertTLCFrame(stackFrames[0], 9, 25, 9, 28, MDL, Context.Empty.cons(null, new StringValue("a"))); // TRUE

		stackFrames = debugger.stepIn();
		assertEquals(3, stackFrames.length);
		assertTLCFrame(stackFrames[2], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[1], 12, 11, 12, 28, RM);
		assertTLCFrame(stackFrames[0], 12, 25, 12, 28, RM); // Node in 'initiator \in Node'

		stackFrames = debugger.stepIn();
		assertEquals(4, stackFrames.length);
		assertTLCFrame(stackFrames[3], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[2], 12, 11, 12, 28, RM);
		assertTLCFrame(stackFrames[1], 12, 25, 12, 28, RM);
		assertTLCFrame(stackFrames[0], 5, 7, 5, 21, MDL); // Def of N1 in MCEcho 

		stackFrames = debugger.stepIn();
		assertEquals(2, stackFrames.length);
		assertTLCFrame(stackFrames[1], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[0], 13, 11, 13, 41, RM); // R \in [Node \X Node -> BOOLEAN]
		
		stackFrames = debugger.stepIn();
		assertEquals(3, stackFrames.length);
		assertTLCFrame(stackFrames[2], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[1], 13, 11, 13, 41, RM);
		assertTLCFrame(stackFrames[0], 13, 11, 13, 11, RM); // R
		
		stackFrames = debugger.stepIn();
		assertEquals(4, stackFrames.length);
		assertTLCFrame(stackFrames[3], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[2], 13, 11, 13, 41, RM);
		assertTLCFrame(stackFrames[1], 13, 11, 13, 11, RM); 
		assertTLCFrame(stackFrames[0], 22, 7, 24, 43, MDL); // [ edge \in (N1 \X N1)... in MCEcho

		stackFrames = debugger.stepOut();
		assertEquals(3, stackFrames.length);
		assertTLCFrame(stackFrames[2], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[1], 13, 11, 13, 41, RM);
		assertTLCFrame(stackFrames[0], 13, 17, 13, 41, RM); // [Node \X Node -> BOOLEAN] in Echo

		stackFrames = debugger.stepOut();
		assertEquals(2, stackFrames.length);
		assertTLCFrame(stackFrames[1], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[0], 15, 11, 15, 32, RM); // IsIrreflexive(R, Node)

		stackFrames = debugger.next();
		assertEquals(2, stackFrames.length);
		assertTLCFrame(stackFrames[1], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[0], 18, 11, 18, 30, RM); // IsSymmetric(R, Node)

		// Breakpoint takes precedence over manual steps.
		debugger.replaceAllBreakpointsWith("Relation", 49);
		stackFrames = debugger.next(2);
		assertEquals(8, stackFrames.length);
		assertTLCFrame(stackFrames[0], 49, 3, 50, 38, "Relation", null); //TODO Replace null with the expected Context.
		// Too lazy to check all the in-between frames.
		assertTLCFrame(stackFrames[7], 12,  8, 21, 30, RM);
		
		// 88888888888888 End of Echo's assumption 88888888888888 //
		
		// Debug type correctness property during Init //
		debugger.replaceAllBreakpointsWith(RM, 167);
		stackFrames = debugger.continue_();
		assertEquals(11, stackFrames.length);
		// Invariants are shown as TLCStateFrames, not TLCActionFrames, which would make
		// the debugger show a predecessor state.
		assertTLCStateFrame(stackFrames[0], 167, 6, 167, 63, RM, Context.Empty);
		
		TLCStateStackFrame frame = (TLCStateStackFrame) stackFrames[0];
		Variable[] trace = frame.getTrace();
		assertEquals(1, trace.length);
		assertEquals(new RecordValue(frame.state), ((DebugTLCVariable) trace[0]).getTLCValue());
		assertEquals("1: <Init line 95, col 9 to line 101, col 43 of module Echo>", trace[trace.length - 1].getName());

		// Debug type correctness property during n0 (next-state relation)
		// (Run to n0, then run to TypeOK)
		debugger.unsetBreakpoints();
		debugger.replaceAllBreakpointsWith(RM, 104);
		stackFrames = debugger.continue_();
		assertEquals(4, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 104, 16, 107, 40, RM, (Context) null, getVars());
		
		debugger.replaceAllBreakpointsWith(RM, 167);
		stackFrames = debugger.continue_();
		assertEquals(11, stackFrames.length);
		assertTLCStateFrame(stackFrames[0], 167, 6, 167, 63, RM, Context.Empty);
		frame = (TLCStateStackFrame) stackFrames[0];
		assertEquals(2, frame.state.getLevel());

		// Replace the previous breakpoint with the same one except for a hit condition
		// corresponding to a trace length of four states.
		debugger.unsetBreakpoints();
		SetBreakpointsArguments sba = createBreakpointArgument(RM, 104);
		sba.getBreakpoints()[0].setHitCondition("5");
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(4, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 104, 16, 107, 40, RM, (Context) null, getVars());

		// Check n0 action has expected number of successor states.
		sba = createBreakpointArgument(RM, 103, 1, 1); // Inline breakpoint set on the LHS of Action definition.
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(1, stackFrames.length);
		assertTLCSuccessorFrame(stackFrames[0], 103, 1, 109, 59, RM, null, 1);

		sba = createBreakpointArgument(RM, 112, 0, 13);
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(4, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 112, 16, 129, 71, RM, (Context) null, getVars());
		
		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}
