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

import org.eclipse.lsp4j.debug.StackFrame;
import org.junit.Test;

import tlc2.output.EC;
import tlc2.util.Context;
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
		debugger.setBreakpoints("Relation", 49);
		stackFrames = debugger.next(2);
		assertEquals(8, stackFrames.length);
		assertTLCFrame(stackFrames[0], 49, 3, 50, 38, "Relation", null); //TODO Replace null with the expected Context.
		// Too lazy to check all the in-between frames.
		assertTLCFrame(stackFrames[7], 12,  8, 21, 30, RM);
		
		// 88888888888888 End of Echo's assumption 88888888888888 //
		
		// Debug type correctness property during Init //
		debugger.setBreakpoints(RM, 167);
		stackFrames = debugger.continue_();
		assertEquals(11, stackFrames.length);
		// Invariants are shown as TLCStateFrames, not TLCActionFrames, which would make
		// the debugger show a predecessor state.
		assertTLCStateFrame(stackFrames[0], 167, 6, 167, 63, RM, Context.Empty);

		// Debug type correctness property during n0 (next-state relation)
		// (Run to n0, then run to TypeOK)
		debugger.unsetBreakpoints();
		debugger.setBreakpoints(RM, 104);
		stackFrames = debugger.continue_();
		assertEquals(3, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 104, 16, 107, 40, RM, (Context) null, getVars());

		debugger.setBreakpoints(RM, 167);
		stackFrames = debugger.continue_();
		assertEquals(10, stackFrames.length);
		assertTLCStateFrame(stackFrames[0], 167, 6, 167, 63, RM, Context.Empty);
		
		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}
