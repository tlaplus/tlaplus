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

import java.util.Arrays;

import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;
import org.eclipse.lsp4j.debug.VariablesArguments;
import org.junit.Test;

import tla2sany.semantic.OpDeclNode;
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
		assertTLCFrame(stackFrames[0], 13, 11, 13, 11, RM); // [Node \X Node -> BOOLEAN] in Echo

		stackFrames = debugger.stepOut();
		assertEquals(2, stackFrames.length);
		assertTLCFrame(stackFrames[1], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[0], 13, 11, 13, 41, RM);

		stackFrames = debugger.next();
		assertEquals(2, stackFrames.length);
		assertTLCFrame(stackFrames[1], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[0], 15, 11, 15, 32, RM); // IsIrreflexive(R, Node)

		stackFrames = debugger.next();
		assertEquals(2, stackFrames.length);
		assertTLCFrame(stackFrames[1], 12,  8, 21, 30, RM);
		assertTLCFrame(stackFrames[0], 15, 11, 15, 32, RM); // IsSymmetric(R, Node)
		

		// Breakpoint takes precedence over manual steps.
		debugger.replaceAllBreakpointsWith("Relation", 49);
		stackFrames = debugger.continue_();
		assertEquals(8, stackFrames.length);
		assertTLCFrame(stackFrames[0], 49, 3, 50, 38, "Relation", null); //TODO Replace null with the expected Context.
		// Too lazy to check all the in-between frames.
		assertTLCFrame(stackFrames[7], 12,  8, 21, 30, RM);
		
		// 88888888888888 End of Echo's assumption 88888888888888 //
		
		// Debug type correctness property during Init //
		debugger.replaceAllBreakpointsWith(RM, 167);
		stackFrames = debugger.continue_();
		assertEquals(13, stackFrames.length);
		// Invariants are shown as TLCStateFrames, not TLCActionFrames, which would make
		// the debugger show a predecessor state.
		assertTLCStateFrame(stackFrames[0], 167, 6, 167, 63, RM, Context.Empty);
		
		TLCStateStackFrame frame = (TLCStateStackFrame) stackFrames[0];
		Variable[] trace = frame.getTrace();
		assertEquals(1, trace.length);
		assertEquals(new RecordValue(frame.state), ((DebugTLCVariable) trace[0]).getTLCValue());
		assertEquals("1: <Init line 95, col 9 to line 101, col 43 of module Echo>", trace[trace.length - 1].getName());

		assertTLCSyntheticStateStackFrame(stackFrames[12], 95, 9, 101, 43, RM, Context.Empty, 1);
		
		// Debug type correctness property during n0 (next-state relation)
		// (Run to n0, then run to TypeOK)
		debugger.unsetBreakpoints();
		debugger.replaceAllBreakpointsWith(RM, 104);
		stackFrames = debugger.continue_();
		assertEquals(5, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 104, 16, 107, 40, RM, (Context) null, getVars());
		assertTLCSyntheticStateStackFrame(stackFrames[4], 95, 9, 101, 43, RM, Context.Empty, 1);
		
		debugger.replaceAllBreakpointsWith(RM, 167);
		stackFrames = debugger.continue_();
		assertEquals(11, stackFrames.length);
		assertTLCStateFrame(stackFrames[0], 167, 6, 167, 63, RM, Context.Empty);
		frame = (TLCStateStackFrame) stackFrames[0];
		assertEquals(2, frame.state.getLevel());
		assertTLCSyntheticStateStackFrame(stackFrames[10], 95, 9, 101, 43, RM, Context.Empty, 1);
		
		// Debug TypeOK with a debug expression breakpoint that is referencing TypeOK via NotTypeOK.
		debugger.unsetBreakpoints();
		SetBreakpointsArguments sba = createBreakpointArgument(RM, 167, "NotNotTypeOK");
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(12, stackFrames.length);
		assertTLCStateFrame(stackFrames[0], 167, 6, 167, 63, RM, Context.Empty);

		// Replace the previous breakpoint with the same one except for a hit condition
		// corresponding to a trace length of four states.
		debugger.unsetBreakpoints();
		sba = createBreakpointArgument(RM, 104);
		sba.getBreakpoints()[0].setHitCondition("5");
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(7, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 104, 16, 107, 40, RM, (Context) null, getVars());
		assertTLCSyntheticStateStackFrame(stackFrames[4], 103, 13, 109, 59, RM, (Context) null, 3);
		assertTLCSyntheticStateStackFrame(stackFrames[5], 103, 13, 109, 59, RM, (Context) null, 2);
		assertTLCSyntheticStateStackFrame(stackFrames[6], 95, 9, 101, 43, RM, Context.Empty, 1);

		sba = createBreakpointArgument(RM, 103, "DebugExpression"); // Inline breakpoint set on the LHS of Action definition.
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(5, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 103, 13, 109, 59, RM, Context.Empty.cons(null, new StringValue("b"))
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")), getVars());

		sba = createBreakpointArgument(RM, 103, "DebugExpression2"); // Inline breakpoint set on the LHS of Action definition.
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(5, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 103, 13, 109, 59, RM, Context.Empty.cons(null, new StringValue("a"))
				.cons(null, new StringValue("a")).cons(null, new StringValue("a")), getVars());

		sba = createBreakpointArgument(RM, 112, 0, 13);
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(15, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 112, 16, 129, 71, RM, (Context) null, getVars());
		
		sba = createBreakpointArgument(RM, 133, "DebugExpression");
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(15, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 133, 16, 138, 40, RM, (Context) null, getVars());

		sba = createBreakpointArgument(MDL, 38, "View");
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(22, stackFrames.length);
		assertTLCStateFrame(stackFrames[0], 38, 9, 38, 12, MDL, Context.Empty);
		
		frame = (TLCStateStackFrame) stackFrames[0];
		constants = frame.getConstants();
		nested = frame.getVariables(constants[0].getVariablesReference());
		assertEquals(4, nested.length);
		assertEquals("I1", nested[0].getName());
		assertEquals("a", nested[0].getValue());
		assertEquals("N1", nested[1].getName());
		assertEquals("{\"a\", \"b\", \"c\"}", nested[1].getValue());
		assertEquals("ProcSet", nested[2].getName());
		assertEquals("{\"a\", \"b\", \"c\"}", nested[2].getValue());
		assertEquals("R1", nested[3].getName());
		assertEquals("(<<\"a\", \"a\">> :> FALSE @@ <<\"a\", \"b\">> :> TRUE @@ <<\"a\", \"c\">> :> TRUE @@ <<\"b\", \"a\">> :> TRUE @@ <<\"b\", \"b\">> :> FALSE @@ <<\"b\", \"c\">> :> TRUE @@ <<\"c\", \"a\">> :> TRUE @@ <<\"c\", \"b\">> :> TRUE @@ <<\"c\", \"c\">> :> FALSE)", nested[3].getValue());

		trace = frame.getTrace();
		assertEquals(12, trace.length);
		assertEquals("1: <Init line 95, col 9 to line 101, col 43 of module Echo>", trace[trace.length - 1].getName());

		final Scope[] scopes = frame.getScopes();
		assertEquals(4, scopes.length);
		final Scope stateScope = Arrays.asList(scopes).stream().filter(s -> s.getName().equals("State")).findFirst().get();
		
		final VariablesArguments args = new VariablesArguments();
		args.setVariablesReference(stateScope.getVariablesReference());
		nested = debugger.variables(args).get().getVariables();
		assertEquals(1, nested.length);
		assertEquals(new RecordValue(frame.state), ((DebugTLCVariable) nested[0]).getTLCValue());

		assertTLCSyntheticStateStackFrame(stackFrames[10], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")),
				12);
		assertTLCSyntheticStateStackFrame(stackFrames[11], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")),
				11);
		assertTLCSyntheticStateStackFrame(stackFrames[12], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("a")).cons(null, new StringValue("a")).cons(null, new StringValue("a")),
				10);
		assertTLCSyntheticStateStackFrame(stackFrames[13], 132, 13, 140, 59, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 9);
		assertTLCSyntheticStateStackFrame(stackFrames[14], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 8);
		assertTLCSyntheticStateStackFrame(stackFrames[15], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 7);
		assertTLCSyntheticStateStackFrame(stackFrames[16], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")), 6);
		assertTLCSyntheticStateStackFrame(stackFrames[17], 103, 13, 109, 59, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")), 5);
		assertTLCSyntheticStateStackFrame(stackFrames[18], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 4);
		assertTLCSyntheticStateStackFrame(stackFrames[19], 103, 13, 109, 59, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 3);
		assertTLCSyntheticStateStackFrame(stackFrames[20], 103, 13, 109, 59, RM, Context.Empty
				.cons(null, new StringValue("a")).cons(null, new StringValue("a")).cons(null, new StringValue("a")), 2);
		assertTLCSyntheticStateStackFrame(stackFrames[21], 95, 9, 101, 43, RM, Context.Empty, 1);

		// Check Next action has expected number of successor states.
		debugger.setSpecBreakpoint();
		stackFrames = debugger.continue_();
		assertEquals(13, stackFrames.length);
		assertTLCNextStatesFrame(stackFrames[0], 151, 20, 151, 23, RM, Context.Empty, 1);

		assertTLCSyntheticStateStackFrame(stackFrames[1], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")),
				12);
		assertTLCSyntheticStateStackFrame(stackFrames[2], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")),
				11);
		assertTLCSyntheticStateStackFrame(stackFrames[3], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("a")).cons(null, new StringValue("a")).cons(null, new StringValue("a")),
				10);
		assertTLCSyntheticStateStackFrame(stackFrames[4], 132, 13, 140, 59, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 9);
		assertTLCSyntheticStateStackFrame(stackFrames[5], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 8);
		assertTLCSyntheticStateStackFrame(stackFrames[6], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 7);
		assertTLCSyntheticStateStackFrame(stackFrames[7], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")), 6);
		assertTLCSyntheticStateStackFrame(stackFrames[8], 103, 13, 109, 59, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")), 5);
		assertTLCSyntheticStateStackFrame(stackFrames[9], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 4);
		assertTLCSyntheticStateStackFrame(stackFrames[10], 103, 13, 109, 59, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 3);
		assertTLCSyntheticStateStackFrame(stackFrames[11], 103, 13, 109, 59, RM, Context.Empty
				.cons(null, new StringValue("a")).cons(null, new StringValue("a")).cons(null, new StringValue("a")), 2);
		assertTLCSyntheticStateStackFrame(stackFrames[12], 95, 9, 101, 43, RM, Context.Empty, 1);

		// Ad-hoc expression-based breakpoint
		
		debugger.unsetBreakpoints();
		sba = createBreakpointArgument(RM, 133, 19, 1, "\\E n \\in Node: inbox[n] = {}"); // Ad-hoc defined expression built from constant and variable value. // TODO Support ctxt, i.e., self!
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(16, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 133, 19, 133, 34, RM, (Context) null, getVars());

		// The last three frames differ from the previous breakpoint hit because BFS
		// advanced to a different part of the state graph.
		assertTLCSyntheticStateStackFrame(stackFrames[5], 132, 13, 140, 59, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")),
				11);
		assertTLCSyntheticStateStackFrame(stackFrames[6], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")),
				10);
		assertTLCSyntheticStateStackFrame(stackFrames[7], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")), 9);

		assertTLCSyntheticStateStackFrame(stackFrames[8], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 8);
		assertTLCSyntheticStateStackFrame(stackFrames[9], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 7);
		assertTLCSyntheticStateStackFrame(stackFrames[10], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")), 6);
		assertTLCSyntheticStateStackFrame(stackFrames[11], 103, 13, 109, 59, RM, Context.Empty
				.cons(null, new StringValue("c")).cons(null, new StringValue("c")).cons(null, new StringValue("c")), 5);
		assertTLCSyntheticStateStackFrame(stackFrames[12], 111, 13, 130, 27, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 4);
		assertTLCSyntheticStateStackFrame(stackFrames[13], 103, 13, 109, 59, RM, Context.Empty
				.cons(null, new StringValue("b")).cons(null, new StringValue("b")).cons(null, new StringValue("b")), 3);
		assertTLCSyntheticStateStackFrame(stackFrames[14], 103, 13, 109, 59, RM, Context.Empty
				.cons(null, new StringValue("a")).cons(null, new StringValue("a")).cons(null, new StringValue("a")), 2);
		assertTLCSyntheticStateStackFrame(stackFrames[15], 95, 9, 101, 43, RM, Context.Empty, 1);

		debugger.unsetBreakpoints();
		sba = createBreakpointArgument(RM, 140, 16, 1, "\\E n \\in Node: inbox'[n] = {}"); // Ad-hoc defined expression built from constant and variable value. // TODO Support ctxt, i.e., self!
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(20, stackFrames.length);
		final OpDeclNode[] vars = getVars();
		assertTLCActionFrame(stackFrames[0], 140, 16, 140, 59, RM, (Context) null, vars[1], vars[2], vars[3], vars[4]);
		
		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}
