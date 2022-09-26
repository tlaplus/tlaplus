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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.eclipse.lsp4j.debug.EvaluateResponse;
import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.Variable;
import org.junit.Test;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tlc2.debug.TLCStateStackFrame.DebuggerValue;
import tlc2.output.EC;
import tlc2.util.Context;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.SetOfRcdsValue;
import tlc2.value.impl.TLCVariable;
import tlc2.value.impl.TupleValue;

public class EWD998ChanDebuggerTest extends TLCDebuggerTestCase {

	private static final String UTILS = "Utils";
	private static final String FOLDER = "EWD998";
	private static final String RM = "EWD998Chan";
	private static final String MDL = "EWD998Chan";

	public EWD998ChanDebuggerTest() {
		super(MDL, FOLDER, EC.ExitStatus.SUCCESS);
	}

	@Test
	public void testSpec() throws Exception {
		StackFrame[] stackFrames = debugger.stackTrace();
		
		// ASSUME in EWD998Chan
		assertEquals(1, stackFrames.length);
		assertTLCFrame(stackFrames[0], 11, 11, RM);
		// prefix depends on where the tests execute.
		assertTrue(stackFrames[0].getSource().getPath().endsWith("test-model/EWD998/EWD998Chan.tla"));
		stackFrames = debugger.stepIn();
		assertEquals(2, stackFrames.length);
		assertTLCFrame(stackFrames[1], 11, 11, RM);
		assertTLCFrame(stackFrames[0], 11, 11, RM);
		
		// Check constant context of ASSUME.
		TLCStackFrame stackFrame = (TLCStackFrame) stackFrames[1];
		Variable[] constants = stackFrame.getConstants();
		assertEquals(2, constants.length);
		
		// Check Watch expressions
		assertEquals(new EvaluateResponse(), stackFrame.getWatch((OpDefNode) null));
		assertEquals(new EvaluateResponse(), stackFrame.getWatch((String) null));
		assertEquals(new EvaluateResponse(), stackFrame.getWatch("Does not exist"));
		
		assertEquals(
				"In evaluation, the identifier counter is either undefined or not an operator.\\nline 43, col 6 to line 43, col 12 of module EWD998Chan",
				stackFrame.getWatch("Init").getResult());
		assertEquals(
				"In evaluation, the identifier inbox is either undefined or not an operator.\\nline 53, col 22 to line 53, col 26 of module EWD998Chan",
				stackFrame.getWatch("InitiateProbe").getResult());
		assertEquals(
				"In evaluation, the identifier inbox is either undefined or not an operator.\\nline 53, col 22 to line 53, col 26 of module EWD998Chan",
				stackFrame.getWatch("System").getResult());
		
		// High-level spec constants (expected to be ordered lexicographically)
		Variable[] consts = stackFrame.getVariables(constants[0].getVariablesReference());
		assertEquals(3, consts.length);
		
		assertEquals("Color", consts[0].getName());
		assertEquals(SetEnumValue.EmptySet.getTypeString(), consts[0].getType());
		assertEquals("{\"white\", \"black\"}", consts[0].getValue());
		assertEquals(2, ((SetEnumValue) ((TLCVariable) consts[0]).getTLCValue()).elems.size());
		// Can be expanded to two atomic values "white" and "black"
		assertEquals(2, stackFrame.getVariables(consts[0].getVariablesReference()).length);
		// Because we always order values lexicographically, the order changes from
		// 'white, black' in the toString of SetEnumValue to 'b, w' in Variable.
		assertEquals("\"black\"", stackFrame.getVariables(consts[0].getVariablesReference())[0].getValue());
		assertEquals("\"white\"", stackFrame.getVariables(consts[0].getVariablesReference())[1].getValue());
		
		assertEquals("Nodes", consts[1].getName());
		assertEquals(SetEnumValue.EmptySet.getTypeString(), consts[1].getType());
		assertEquals("{0, 1, 2}", consts[1].getValue());
		assertEquals(3, ((SetEnumValue) ((TLCVariable) consts[1]).getTLCValue()).elems.size());
		
		// This one tests if we correctly handle infinite domains, i.e. the Int.
		assertEquals("Token", consts[2].getName());
		assertEquals("SetOfRcdsValue: a set of the form [d1 : S1, ... , dN : SN]", consts[2].getType());
		assertEquals("[color: {\"white\", \"black\"}, q: Int, pos: 0..2]", consts[2].getValue());
		assertEquals(3, ((SetOfRcdsValue) ((TLCVariable) consts[2]).getTLCValue()).names.length);
		
		// nested of Token
		consts = stackFrame.getVariables(consts[2].getVariablesReference());
		// TODO For now, if one of the values has infinite domain, none of the values
		// can be expanded.
		assertEquals(0, consts.length);
		
		// Low-level spec constants
		consts = stackFrame.getVariables(constants[1].getVariablesReference());
		assertEquals(6, consts.length);
		
		assertEquals("BasicMsg", consts[0].getName());
		assertEquals("SetOfRcdsValue: a set of the form [d1 : S1, ... , dN : SN]", consts[0].getType());
		assertEquals("{[type |-> \"pl\"]}", consts[0].getValue());
		
		assertEquals("Color", consts[1].getName());
		assertEquals(SetEnumValue.EmptySet.getTypeString(), consts[1].getType());
		assertEquals("{\"white\", \"black\"}", consts[1].getValue());
		
		assertEquals("Message", consts[2].getName());
		assertEquals("SetCupValue: a set of the form S \\cup T", consts[2].getType());
		assertEquals("[color: {\"white\", \"black\"}, type: {\"tok\"}, q: Int] \\cup {[type |-> \"pl\"]}", consts[2].getValue());
		
		assertEquals("N", consts[3].getName());
		assertEquals(IntValue.ValZero.getTypeString(), consts[3].getType());
		assertEquals("3", consts[3].getValue());
		
		assertEquals("Nodes", consts[4].getName());
		assertEquals(SetEnumValue.EmptySet.getTypeString(), consts[4].getType());
		assertEquals("{0, 1, 2}", consts[4].getValue());
		
		assertEquals("TokenMsg", consts[5].getName());
		assertEquals("SetOfRcdsValue: a set of the form [d1 : S1, ... , dN : SN]", consts[5].getType());
		assertEquals("[color: {\"white\", \"black\"}, type: {\"tok\"}, q: Int]", consts[5].getValue());
		
		
		// *********************************************************** //
		
		// Assert breakpoints are correctly verified, which indicates to users where
		// breakpoints can be placed.
		final Set<Integer> lines = IntStream.of(11, 13, 14, 15, 24, 27, 28, 29, 30, 31, 36, 37, 39, 40, 41, 45, 47, 48,
				49, 50, 51, 53, 57, 58, 59, 60, 61, 62, 64, 66, 67, 73, 75, 77, 80, 83, 84, 86, 88, 90, 91, 94, 95, 96,
				98, 103, 105, 113, 114, 123, 124, 125, 126, 127, 128, 133, 140, 141, 144, 150, 153, 154, 155, 156, 158,
				160, 162, 168, 171).boxed().collect(Collectors.toSet());
		lines.forEach(i -> {
			assertTrue(String.format("line %s", i),
					debugger.replaceAllBreakpointsWithUnchecked(FOLDER, i)[0].isVerified());
		});
		IntStream.rangeClosed(1, 171).filter(line -> !lines.contains(line)).forEach(i -> {
			assertFalse(String.format("line %s", i),
					debugger.replaceAllBreakpointsWithUnchecked(FOLDER, i)[0].isVerified());
		});

		assertTrue(debugger.replaceAllBreakpointsWith(RM, 102)[0].isVerified());
		assertFalse(debugger.replaceAllBreakpointsWith(RM, 103)[0].isVerified());
		assertTrue(debugger.replaceAllBreakpointsWith(RM, 104)[0].isVerified());
		assertFalse(debugger.replaceAllBreakpointsWith(RM, 105)[0].isVerified());
		assertFalse(debugger.replaceAllBreakpointsWith(RM, 105)[0].isVerified());
		assertTrue(debugger.replaceAllBreakpointsWith(RM, 107)[0].isVerified());

		// *********************************************************** //
		
		final OpDeclNode[] vars = getVars();

		debugger.replaceAllBreakpointsWith(RM, 49);
		stackFrames = debugger.continue_();
		assertTLCStateFrame(stackFrames[0], 49, 49, RM, vars[1]);
		
		// Debug an operator that is evaluated as part of the refinement mapping and known to
		// consist of a bunch of LazyValues.  LazyValues are tricky because the debugger
		// unlazies them, which has to be ignored by DebugTool.  Otherwise, the debugger
		// debugs itself and deadlocks.
		debugger.replaceAllBreakpointsWith(UTILS, 13);
		stackFrames = debugger.continue_();
		
		int i = 17;
		assertEquals(i, stackFrames.length);
		assertTLCStateFrame(stackFrames[--i], 43, 49, RM, vars);
		assertTLCStateFrame(stackFrames[--i], 43, 43, RM, vars);
		assertTLCStateFrame(stackFrames[--i], 44, 46, RM, vars[0], vars[1], vars[3]);
		assertTLCStateFrame(stackFrames[--i], 48, 48, RM, vars[0], vars[1]);
		assertTLCStateFrame(stackFrames[--i], 49, 49, RM, vars[1]);
		assertTLCStateFrame(stackFrames[--i], 49, 49, RM);
		//186 186 EWD998Inv == EWD998!Inv
		assertTLCStateFrame(stackFrames[--i], 187, 187, RM);
		assertTLCStateFrame(stackFrames[--i], 166, 181, RM);

		// action, counter, color, pending, and token are part of the context because
		// this is debugging the refinement mapping.
		Map<String, String> allVariables = new HashMap<>();
		allVariables.put("pending", "(0 :> 0 @@ 1 :> 0 @@ 2 :> 0)");
		allVariables.put("token", "[pos |-> 0, q |-> 0, color |-> \"black\"]");
		allVariables.put("counter", "(0 :> 0 @@ 1 :> 0 @@ 2 :> 0)");
		allVariables.put("N", "3");
		allVariables.put("active", "(0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE)");
		allVariables.put("color", "(0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\")");
		assertTLCStateFrame(stackFrames[--i], 150, 162, FOLDER, allVariables);
		assertTLCStateFrame(stackFrames[--i], 150, 150, FOLDER, allVariables);
		assertTLCStateFrame(stackFrames[--i], 150, 150, FOLDER, allVariables);
		//150 150  B in '/\ P0:: B = Reduce(sum, counter, 0, N-1, 0)'
		assertTLCStateFrame(stackFrames[--i], 150, 150, FOLDER, allVariables);
		assertTLCStateFrame(stackFrames[--i], 133, 133, FOLDER, allVariables);
		
		allVariables.put("op", "sum(a,b) == a+b");
		allVariables.put("fun", "(0 :> 0 @@ 1 :> 0 @@ 2 :> 0)");
		allVariables.put("from", "0");
		allVariables.put("to", "2");
		allVariables.put("base", "0");
		assertTLCStateFrame(stackFrames[--i], 11, 14, UTILS, allVariables);
		allVariables.put("reduced", "(0 :> 0 @@ 1 :> 0 @@ 2 :> 0)");
		assertTLCStateFrame(stackFrames[--i], 14, 14, UTILS, allVariables);
		allVariables.put("i", "2");
		assertTLCStateFrame(stackFrames[--i], 12, 13, UTILS, allVariables);
		assertTLCStateFrame(stackFrames[--i], 13, 13, UTILS, allVariables);
		
		// 88888888888888888888888 Check Stack Variables 888888888888888888888888 //
		
		// InitiateProbe sub-action
		debugger.replaceAllBreakpointsWith(RM, 71);
		stackFrames = debugger.continue_();
		List<Variable> stackVariables = ((TLCStackFrame) stackFrames[5]).getStackVariables(new ArrayList<>());
		assertEquals(1, stackVariables.size());
		assertEquals("TRUE", stackVariables.get(0).getValue());
		assertEquals("inbox[0][j].type=\"tok\"", stackVariables.get(0).getName());
		assertEquals(BoolValue.ValFalse.getTypeString(), stackVariables.get(0).getType());

		stackVariables = ((TLCStackFrame) stackFrames[3]).getStackVariables(new ArrayList<>());
		assertEquals(2, stackVariables.size());
		assertEquals("TRUE", stackVariables.get(1).getValue());
		assertEquals("inbox[0][j].type=\"tok\"", stackVariables.get(1).getName());
		assertEquals(BoolValue.ValFalse.getTypeString(), stackVariables.get(1).getType());
		assertEquals("TRUE", stackVariables.get(0).getValue());
		assertEquals("inbox[0][j].color=\"black\"", stackVariables.get(0).getName());
		assertEquals(BoolValue.ValFalse.getTypeString(), stackVariables.get(0).getType());
		
		// PassToken sub-action
		debugger.replaceAllBreakpointsWith(RM, 85);
		stackFrames = debugger.continue_();
		stackVariables = ((TLCStackFrame) stackFrames[6]).getStackVariables(new ArrayList<>());
		assertEquals(1, stackVariables.size());
		assertEquals("TRUE", stackVariables.get(0).getValue());
		assertEquals("~active[i]", stackVariables.get(0).getName());
		assertEquals(BoolValue.ValFalse.getTypeString(), stackVariables.get(0).getType());

		stackVariables = ((TLCStackFrame) stackFrames[3]).getStackVariables(new ArrayList<>());
		assertEquals(2, stackVariables.size());
		assertEquals("TRUE", stackVariables.get(1).getValue());
		assertEquals("~active[i]", stackVariables.get(1).getName());
		assertEquals(BoolValue.ValFalse.getTypeString(), stackVariables.get(1).getType());
		assertEquals("TRUE", stackVariables.get(0).getValue());
		assertEquals("inbox[i][j].type=\"tok\"", stackVariables.get(0).getName());
		assertEquals(BoolValue.ValFalse.getTypeString(), stackVariables.get(0).getType());
		
		// 88888888888888888888888888888888888888888888888888888888888888 //
		
		// Step through the evaluation of a mildly complex expression. 
		debugger.replaceAllBreakpointsWith(RM, 119);
		stackFrames = debugger.continue_();
		assertEquals(9, stackFrames.length);
		Context context = Context.Empty.cons(null, IntValue.ValOne).cons(null, IntValue.ValOne).cons(null, IntValue.ValOne);
		assertTLCActionFrame(stackFrames[0], 119, 119, RM, context, vars[3]);

		stackFrames = debugger.stepIn();
		assertEquals(10, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 119, 119, RM, context, vars[3]);

		stackFrames = debugger.stepIn(3);
		assertEquals(11, stackFrames.length);
		Set<Variable> variables = new HashSet<>();
		variables.add(createVariable("i","1",IntValue.ValZero.getTypeString()));
		variables.add(createVariable("j","1",IntValue.ValZero.getTypeString()));
		variables.add(createVariable("@","<<[type |-> \"pl\"]>>",TupleValue.EmptyTuple.getTypeString()));
		assertTLCActionFrame(stackFrames[0], 119, 44, 119, 57, RM, variables, vars[3]);

		stackFrames = debugger.stepIn();
		assertEquals(12, stackFrames.length);
		variables.add(createVariable("s","<<[type |-> \"pl\"]>>",TupleValue.EmptyTuple.getTypeString()));
		assertTLCActionFrame(stackFrames[0], 29, 29, UTILS, variables, vars[3]);

		stackFrames = debugger.stepIn(13);
		assertEquals(10, stackFrames.length);
		variables = new HashSet<>();
		variables.add(createVariable("i","1",IntValue.ValZero.getTypeString()));
		variables.add(createVariable("j","1",IntValue.ValZero.getTypeString()));
		assertTLCActionFrame(stackFrames[0], 120, 6, 120, 19, RM, variables);
		
		// 8888888888888888888 Invariant TypeOK 8888888888888888888 //
		debugger.replaceAllBreakpointsWith(RM, 29);
		stackFrames = debugger.continue_();
		assertEquals(11, stackFrames.length);
		assertTLCStateFrame(stackFrames[0], 29, 3, 37, 25, RM, Context.Empty);
		
		// 8888888888888888888 Invariant EWD998!Inv 8888888888888888888 //
		debugger.replaceAllBreakpointsWith(FOLDER, 150);
		stackFrames = debugger.continue_();
		assertEquals(11, stackFrames.length);
		assertTLCStateFrame(stackFrames[0], 150, 3, 162, 34, FOLDER, (Context) null); //TODO Assert context that contains the refinement mapping
		
		// 8888888888888888888 Test resolving a location (e.g. editor hovering) to a value 888888888888888 //
		debugger.replaceAllBreakpointsWith(RM, 120);
		debugger.continue_();
		
		// inbox
		EvaluateResponse var = debugger.evaluate(RM, "inbox", 118, 14, 118, 18);
		assertEquals("FcnRcdValue: a function  of the form (d1 :> e1 @@ ... @@ dN :> eN)", var.getType());
		assertNotEquals(0, var.getVariablesReference());
		assertEquals("(0 :> <<[color |-> \"black\", type |-> \"tok\", q |-> 0]>> @@ 1 :> <<[type |-> \"pl\"]>> @@ 2 :> <<>>)", var.getResult());
		var = debugger.evaluate(RM, "inbox", 119, 24, 119, 28);
		assertEquals("FcnRcdValue: a function  of the form (d1 :> e1 @@ ... @@ dN :> eN)", var.getType());
		assertNotEquals(0, var.getVariablesReference());
		assertEquals("(0 :> <<[color |-> \"black\", type |-> \"tok\", q |-> 0]>> @@ 1 :> <<[type |-> \"pl\"]>> @@ 2 :> <<>>)", var.getResult());
		
		// inbox'
		var = debugger.evaluate(RM, "inbox", 119, 14, 119, 19);
		assertEquals("FcnRcdValue: a function  of the form (d1 :> e1 @@ ... @@ dN :> eN)", var.getType());
		assertNotEquals(0, var.getVariablesReference());
		assertEquals("(0 :> <<[color |-> \"black\", type |-> \"tok\", q |-> 0]>> @@ 1 :> <<>> @@ 2 :> <<>>)", var.getResult());

		// i
		var = debugger.evaluate(RM, "i", 109, 9, 109, 9);
		assertEquals(IntValue.ValZero.getTypeString(), var.getType());
		assertEquals(0, var.getVariablesReference());
		assertEquals("1", var.getResult());
		var = debugger.evaluate(RM, "i", 111, 35, 111, 35);
		assertEquals(IntValue.ValZero.getTypeString(), var.getType());
		assertEquals(0, var.getVariablesReference());
		assertEquals("1", var.getResult());
		var = debugger.evaluate(RM, "i", 115, 34, 115, 34);
		assertEquals(IntValue.ValZero.getTypeString(), var.getType());
		assertEquals(0, var.getVariablesReference());
		assertEquals("1", var.getResult());
		
		// j in \E j \in ... no longer in the current scope (ctxt).
		var = debugger.evaluate(RM, "j", 117, 9, 117, 9);
		assertEquals("FormalParamNode", var.getType());
		assertEquals("line 117, col 9 to line 117, col 9 of module EWD998Chan", var.getResult());
		var = debugger.evaluate(RM, "j", 118, 23, 118, 23);
		assertEquals("LazyValue: a value represented in lazy form", var.getType());
		assertEquals("<LAZY line 118, col 23 to line 118, col 23 of module EWD998Chan>", var.getResult());
		var = debugger.evaluate(RM, "j", 119, 56, 119, 56);
		assertEquals("LazyValue: a value represented in lazy form", var.getType());
		assertEquals("<LAZY line 119, col 56 to line 119, col 56 of module EWD998Chan>", var.getResult());

		// PassToken
		debugger.replaceAllBreakpointsWith(RM, 81);
		debugger.continue_();
		
		// inbox[i][j].type (record field)
		var = debugger.evaluate(RM, "type", 77, 26, 77, 29);
		// TODO Evaluating record fields is not yet supported. In case of
		// inbox[i][j].type, we will even have to backtrack to the node representing
		// inbox in the result of SemanticNode#pathTo(77 26 77 29), apply [i][j],
		// resolve the StringNode representing type to its StringValue, and select it
		// from the RecordValue.

		debugger.replaceAllBreakpointsWith(RM, 85);
		debugger.continue_();

		// inbox
		var = debugger.evaluate(RM, "inbox", 80, 28, 80, 32);
		assertEquals("FcnRcdValue: a function  of the form (d1 :> e1 @@ ... @@ dN :> eN)", var.getType());
		assertNotEquals(0, var.getVariablesReference());
		assertEquals("(0 :> <<>> @@ 1 :> <<>> @@ 2 :> <<[color |-> \"white\", type |-> \"tok\", q |-> 0]>>)", var.getResult());
		
		// inbox' (not yet evaluated/"assigned")
		var = debugger.evaluate(RM, "inbox", 80, 18, 80, 23);
		assertEquals(DebuggerValue.NOT_EVALUATED, var.getResult());
		
		// lhs/rhs refinement mapping
		debugger.replaceAllBreakpointsWith(RM, 179);
		debugger.continue_();
		// RHS shows the value of the active variable
		var = debugger.evaluate(RM, "active", 166, 43, 166, 48);
		assertEquals("FcnRcdValue: a function  of the form (d1 :> e1 @@ ... @@ dN :> eN)", var.getType());
		assertNotEquals(0, var.getVariablesReference());
		assertEquals("(0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE)", var.getResult());

		// LHS must not show the value of the active variable in the current state. In
		// case of the test case, the value of active in EWD998 and EWD998Chan happens
		// to be indeed identical, but in other refinement mappings this is not
		// necessarily the case.  The token and pending variable don't match the case
		// we want to test, which is identical variables in high- and low-level spec.
		var = debugger.evaluate(RM, "active", 166, 33, 166, 40);
		assertEquals("line 166, col 33 to line 166, col 40 of module EWD998Chan", var.getResult());


		debugger.unsetBreakpoints();
		SetBreakpointsArguments sba = createBreakpointArgument(RM, 107);
		sba.getBreakpoints()[0].setHitCondition("2");
		debugger.setBreakpoints(sba);
		
		// before the UNCHANGED is evaluated
		stackFrames = debugger.continue_();
		assertEquals(7, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 107, 6, 107, 32, RM, (Context) null, vars[0], vars[1]);

		// evaluate the UNCHANGED
		stackFrames = debugger.stepIn();
		assertEquals(8, stackFrames.length);
		assertTLCActionFrame(stackFrames[0], 107, 6, 107, 32, RM, (Context) null);

		// Run to the state-constraint and a hit condition.
		debugger.unsetBreakpoints();
		sba = createBreakpointArgument(RM, 148);
		sba.getBreakpoints()[0].setHitCondition("3");
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(9, stackFrames.length);
		assertTLCStateFrame(stackFrames[0], 148, 3, 153, 45, RM, Context.Empty);

		// Check SendMsg action has expected number of successor states.
		sba = createBreakpointArgument(RM, 96, 3, 1); // Inline breakpoint set on the LHS of Action definition.
		debugger.setBreakpoints(sba);
		stackFrames = debugger.continue_();
		assertEquals(1, stackFrames.length);
		assertTLCSuccessorFrame(stackFrames[0], 96, 1, 107, 32, RM, Context.Empty.cons(null, IntValue.ValOne).cons(null, IntValue.ValOne), 1);
		
		stackFrame = (TLCStackFrame) stackFrames[0];
		assertEquals(new EvaluateResponse(), stackFrame.getWatch((OpDefNode) null));
		assertEquals(new EvaluateResponse(), stackFrame.getWatch((String) null));
		assertEquals(new EvaluateResponse(), stackFrame.getWatch("Does not exist"));
		
		assertEquals("FALSE", stackFrame.getWatch("Init").getResult());
		assertEquals("FALSE", stackFrame.getWatch("InitiateProbe").getResult());
		assertEquals("FALSE", stackFrame.getWatch("System").getResult());
		assertEquals("FALSE", stackFrame.getWatch("Environment").getResult());
		assertEquals("FALSE", stackFrame.getWatch("Next").getResult());
		assertEquals("FALSE", stackFrame.getWatch("Spec").getResult());
		assertEquals("TRUE", stackFrame.getWatch("StateConstraint").getResult());
		assertEquals("2", stackFrame.getWatch("tpos").getResult());
		assertEquals("TRUE", stackFrame.getWatch("Stop").getResult());
		assertEquals("TRUE", stackFrame.getWatch("ActionConstraint").getResult());
		
		final EvaluateResponse er = stackFrame.getWatch("EnabledAlias");
		assertNotNull(er);
		assertEquals(
				"[InitiateProbe |-> FALSE, PassToken |-> TRUE, SendMsg |-> TRUE, RecvMsg |-> FALSE, Deactivate |-> TRUE]",
				er.getResult());
		assertNotEquals(0, er.getVariablesReference());
		Variable[] frob = stackFrame.getVariables(er.getVariablesReference());
		assertEquals(5, frob.length);
		assertEquals("Deactivate", frob[0].getName());
		assertEquals("TRUE", frob[0].getValue());
		assertEquals("InitiateProbe", frob[1].getName());
		assertEquals("FALSE", frob[1].getValue());
		assertEquals("PassToken", frob[2].getName());
		assertEquals("TRUE", frob[2].getValue());
		assertEquals("RecvMsg", frob[3].getName());
		assertEquals("FALSE", frob[3].getValue());
		assertEquals("SendMsg", frob[4].getName());
		assertEquals("TRUE", frob[4].getValue());
				
		// Remove all breakpoints and run the spec to completion.
		debugger.unsetBreakpoints();
		debugger.continue_();
	}
}
