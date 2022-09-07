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
import static org.junit.Assert.assertTrue;

import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;
import org.junit.Test;

import tla2sany.semantic.OpDeclNode;
import tlc2.output.EC;
import tlc2.util.Context;
import tlc2.value.impl.IntValue;

public class EWD840DebuggerTest extends TLCDebuggerTestCase {

	// MC02 is the spec that extends EWD840 and assigns values to constants for TLC.
	private static final String RM = "EWD840";
	private static final String MDL = "MC02";

	public EWD840DebuggerTest() {
		super(MDL, RM, EC.ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void testSpec() throws Exception {
		StackFrame[] stackFrames = debugger.stackTrace();
		assertEquals(1, stackFrames.length);

		assertTLCFrame(stackFrames[0], 5, 5, RM);
		// prefix depends on where the tests execute.
		assertTrue(stackFrames[0].getSource().getPath().endsWith("test-model/EWD840/EWD840.tla"));
		stackFrames = debugger.stepIn();
		assertEquals(2, stackFrames.length);
		assertTLCFrame(stackFrames[1], 5, 5, RM);
		assertTLCFrame(stackFrames[0], 5, 5, RM);

		// Assert the constants of EWD840 and MC02.
		final TLCStackFrame f = (TLCStackFrame) stackFrames[0];
		final Variable[] variables = f.getVariables(f.getConstantsId());
		assertEquals(2, variables.length);
		assertEquals(RM, variables[0].getName());
		Variable[] nested = f.getVariables(variables[0].getVariablesReference());
		assertEquals(3, nested.length);
		assertEquals("Color", nested[0].getName());
		assertEquals("{\"white\", \"black\"}", nested[0].getValue());
		assertEquals("Nodes", nested[1].getName());
		assertEquals("{0, 1}", nested[1].getValue());
		assertEquals("const_143073460396411000", nested[2].getName());
		assertEquals("2", nested[2].getValue());
		
		assertEquals(MDL, variables[1].getName());
		nested = f.getVariables(variables[1].getVariablesReference());
		assertEquals(1, nested.length);
		assertEquals("const_143073460396411000", nested[0].getName());
		assertEquals("2", nested[0].getValue());
		
		final OpDeclNode[] vars = getVars();
		
		debugger.replaceAllBreakpointsWith(RM,23);

		// The spec has 16 initial states over which we will continue each time checking
		// the stack frames:
		for (int i = 0; i < 16; i++) { //64
			stackFrames = debugger.continue_();

			assertEquals(5, stackFrames.length);
			assertTLCStateFrame(stackFrames[4], 20, 23, RM, vars);
			assertTLCStateFrame(stackFrames[3], 20, 20, RM, vars);
			assertTLCStateFrame(stackFrames[2], 21, 21, RM, vars[0], vars[2], vars[3]);
			assertTLCStateFrame(stackFrames[1], 22, 22, RM, vars[0], vars[2]);
			assertTLCStateFrame(stackFrames[0], 23, 23, RM, vars[2]);

			// TODO: The semantics of continue are broken because we hit the same line
			// breakpoint again, which is not what one would "continue" to do.
			stackFrames = debugger.continue_();

			assertEquals(6, stackFrames.length);
			assertTLCStateFrame(stackFrames[5], 20, 23, RM, vars);
			assertTLCStateFrame(stackFrames[4], 20, 20, RM, vars);
			assertTLCStateFrame(stackFrames[3], 21, 21, RM, vars[0], vars[2], vars[3]);
			assertTLCStateFrame(stackFrames[2], 22, 22, RM, vars[0], vars[2]);
			assertTLCStateFrame(stackFrames[1], 23, 23, RM, vars[2]);
			assertTLCStateFrame(stackFrames[0], 23, 23, RM);
		}

		// Debug the InitiateProbe action of the next-state relation.
		debugger.replaceAllBreakpointsWith(RM, 26);
		stackFrames = debugger.continue_();

		// First frame captures the complete action.
		assertEquals(2, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 26, 31, RM, vars);

		// Second frame captures the first line.
		stackFrames = debugger.stepIn();
		assertEquals(3, stackFrames.length);
		assertTLCActionFrame(stackFrames[1], 26, 31, RM, vars);
		assertTLCActionFrame(stackFrames[0], 26, 26, RM, vars);

		// Third frame.
		stackFrames = debugger.stepIn();
		assertEquals(4, stackFrames.length);
		assertTLCActionFrame(stackFrames[2], 26, 31, RM, vars);
		assertTLCActionFrame(stackFrames[1], 26, 26, RM, vars);
		assertTLCActionFrame(stackFrames[0], 26, 26, RM, vars);

		// Fourth frame.
		stackFrames = debugger.stepIn(2);
		assertEquals(4, stackFrames.length);
		assertTLCActionFrame(stackFrames[2], 26, 31, RM, vars);
		assertTLCActionFrame(stackFrames[1], 26, 26, RM, vars);
		assertTLCActionFrame(stackFrames[0], 27, 27, RM, vars);

		// Debug the SendMsg action of the next-state relation.
		debugger.replaceAllBreakpointsWith(RM, 46);
		stackFrames = debugger.continue_();
		assertEquals(5, stackFrames.length);
		Context context = Context.Empty.cons(null, IntValue.ValOne).cons(null, IntValue.ValOne);
		/*
		  /\ active[i]
		  /\ \E j \in Nodes \ {i} :
		        /\ active' = [active EXCEPT ![j] = TRUE]
		        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
		  /\ UNCHANGED <<tpos, tcolor>>
		 */
		assertTLCActionFrame(stackFrames[3], 44, 48, RM, context, vars);
		/*
		  /\ active[i]
		 */
		assertTLCActionFrame(stackFrames[2], 44, 44, RM, context, vars);
		/*
		  /\ \E j \in Nodes \ {i} :
		        /\ active' = [active EXCEPT ![j] = TRUE]
		        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
		 */
		assertTLCActionFrame(stackFrames[1], 45, 47, RM, context, vars);
		/*
		        /\ active' = [active EXCEPT ![j] = TRUE]
		        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
		 */
		context = context.cons(null, IntValue.ValZero);
		assertTLCActionFrame(stackFrames[0], 46, 47, RM, context, vars);

		/*
        		/\ active' = [active EXCEPT ![j] = TRUE]
		 */
		stackFrames = debugger.stepIn();
		assertEquals(6, stackFrames.length);
		context = Context.Empty.cons(null, IntValue.ValOne).cons(null, IntValue.ValOne);
		assertTLCActionFrame(stackFrames[4], 44, 48, RM, context, vars);
		assertTLCActionFrame(stackFrames[3], 44, 44, RM, context, vars);
		assertTLCActionFrame(stackFrames[2], 45, 47, RM, context, vars);
		context = context.cons(null, IntValue.ValZero);
		assertTLCActionFrame(stackFrames[1], 46, 47, RM, context, vars);
		assertTLCActionFrame(stackFrames[0], 46, 46, RM, context, vars);

		/*
				[active EXCEPT ![j] = TRUE]
				The breakpoint on this line (46) means that step in/out/over
				takes precedence.
		 */
		stackFrames = debugger.next();
		assertEquals(7, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 46, 46, RM, context, vars);
		/*
		        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
		 */
		stackFrames = debugger.next(4);
		assertEquals(8, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 47, 47, RM, context, vars[0], vars[2], vars[3]);

		/*
  				/\ UNCHANGED <<tpos, tcolor>>
		 */
		stackFrames = debugger.stepIn(8);
		assertEquals(8, stackFrames.length);
		context = Context.Empty.cons(null, IntValue.ValOne).cons(null, IntValue.ValOne);
		assertTLCActionFrame(stackFrames[0], 48, 48, RM, context, vars[0], vars[2]);
		
		// 8888888888888888888 State Constraint 8888888888888888888 //
		debugger.replaceAllBreakpointsWith(MDL, 16);
		stackFrames = debugger.continue_();
		stackFrames = debugger.stepIn(13);
		assertEquals(12, stackFrames.length);
		assertTLCStateFrame(stackFrames[0], 16, 54, 16, 64, MDL, Context.Empty.cons(null, IntValue.ValZero));
		Variable[] contextVariables = ((TLCStateStackFrame) stackFrames[0]).getVariables();
		assertNotNull(contextVariables);
		assertEquals(1, contextVariables.length);
		Variable variable = contextVariables[0];
		assertEquals("node", variable.getName());
		assertEquals(IntValue.ValZero.getTypeString(), variable.getType());
		assertEquals("0", variable.getValue());
		
		// 8888888888888888888 Action Constraint 8888888888888888888 //
		debugger.replaceAllBreakpointsWith(MDL, 19);
		stackFrames = debugger.continue_();
		assertEquals(10, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 19, 21, MDL);
		
		// 8888888888888888888 Invariant Inv 8888888888888888888 //
		debugger.replaceAllBreakpointsWith(RM, 94);
		stackFrames = debugger.continue_();
		assertEquals(11, stackFrames.length);
		assertTLCStateFrame(stackFrames[0], 94, 3, 96, 26, RM, Context.Empty);

		final int successors = 1;
		SetBreakpointsArguments sba = createBreakpointArgument(RM, 25, 3, successors);
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(1, stackFrames.length);
		assertTLCSuccessorFrame(stackFrames[0], 25, 1, 31, 25, RM, Context.Empty, successors);

		// 8888888888888888888 ALIAS Alias 8888888888888888888 //

		// Error trace is six states long on which we evaluate the alias expression six
		// times. By definition, an alias expression is evaluated on a pair of states.
		// Let s1 be the initial state and let s2 to s6 be the successor states in the
		// trace with s6 the state that violates the invariant.  The for loop below
		// evaluates the alias expression for the pairs (s1, s2), (s2, s3), (s3, s4),
		// (s4, s5), (s5, s6).  For s6, the alias expression is then evaluated on the
		// pair (s6, s6).  This is done after the for loop.
		debugger.replaceAllBreakpointsWith(MDL, 33);
		for (int i = 0; i < 5; i++) {
			stackFrames = debugger.continue_();
			assertEquals(8, stackFrames.length);
			// null context to ignore TLCExt!Trace in context added via Tool#evalAlias.
			assertTLCActionFrame(stackFrames[0], 33, 20, 33, 49, MDL, (Context) null);
			assertTLCActionFrame(stackFrames[1], 28, 5, 34, 5, MDL, (Context) null);
			assertTLCActionFrame(stackFrames[2], 53, 6, 53, 38, RM, context);
			assertTLCActionFrame(stackFrames[3], 53, 6, 53, 38, RM, context, vars[0], vars[2], vars[3]);
			assertTLCActionFrame(stackFrames[4], 52, 6, 52, 43, RM, context, vars);
			assertTLCActionFrame(stackFrames[5], 51, 6, 51, 14, RM, context, vars);
			assertTLCActionFrame(stackFrames[6], 51, 3, 53, 38, RM, context, vars);
		}
		stackFrames = debugger.continue_();
		assertEquals(8, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 33, 20, 33, 49, MDL, (Context) null);
		assertTLCActionFrame(stackFrames[1], 28, 5, 34, 5, MDL, (Context) null);
		assertTLCActionFrame(stackFrames[2], 53, 6, 53, 38, RM, context);
		assertTLCActionFrame(stackFrames[3], 53, 6, 53, 38, RM, context, vars[0], vars[2], vars[3]);
		assertTLCActionFrame(stackFrames[4], 52, 6, 52, 43, RM, context, vars);
		assertTLCActionFrame(stackFrames[5], 51, 6, 51, 14, RM, context, vars);
		assertTLCActionFrame(stackFrames[6], 51, 3, 53, 38, RM, context, vars);
		assertTLCSuccessorFrame(stackFrames[7], 50, 1, 53, 38, RM, context, 1);

		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}
