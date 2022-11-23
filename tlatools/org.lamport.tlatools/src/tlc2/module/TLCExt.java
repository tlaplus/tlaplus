/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved.
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
package tlc2.module;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Scanner;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.LevelConstants;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.StringNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.overrides.Evaluation;
import tlc2.overrides.TLAPlusOperator;
import tlc2.tool.Action;
import tlc2.tool.EvalException;
import tlc2.tool.ModelChecker;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.TLCStateMutExt;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.util.IdThread;
import tlc2.value.Values;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.CounterExample;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.Assert;
import util.Assert.TLCRuntimeException;

public class TLCExt {
	public static final long serialVersionUID = 20210223L;

	@Evaluation(definition = "AssertError", module = "TLCExt", warn = false, silent = true)
	public synchronized static Value assertError(final Tool tool, final ExprOrOpArgNode[] args, final Context c,
			final TLCState s0, final TLCState s1, final int control, final CostModel cm) {

		// Check expected err is a string.
		Assert.check(args[0] instanceof StringNode, "In computing AssertError, a non-string expression (" + args[0]
				+ ") was used as the err " + "of an AssertError(err, exp).");

		try {
			tool.eval(args[1], c, s0, s1, control, cm);
		} catch (EvalException | TLCRuntimeException e) {
			final StringValue err = (StringValue) tool.eval(args[0], c, s0);
			if (err.val.equals(e.getMessage())) {
				return BoolValue.ValTrue;
			}
		}
		return BoolValue.ValFalse;
	}

	private static final Scanner scanner = new Scanner(System.in);

	// This is likely only useful with a single worker, but let's synchronize
	// anyway.
	@Evaluation(definition = "PickSuccessor", module = "TLCExt", warn = false, silent = true, minLevel = LevelConstants.ActionLevel)
	public synchronized static Value pickSuccessor(final Tool tool, final ExprOrOpArgNode[] args, final Context c,
			final TLCState s0, final TLCState s1, final int control, final CostModel cm) {

		// TLC checks action constraints before it checks if states are new or not. Exclude seen states here
		// to not repeatedly ask a user to extend a behavior with the same state over and over again.
		try {
			if (TLCGlobals.mainChecker != null // simulation mode does not remember seen states.
					&& ((ModelChecker) TLCGlobals.mainChecker).theFPSet.contains(s1.fingerPrint())) {
				// If it is a seen state it is by definition in the model.
				return BoolValue.ValTrue;
			}
		} catch (IOException notExpectedToHappen) {
			notExpectedToHappen.printStackTrace();
			return BoolValue.ValTrue;
		}

		// Eval expression and only let user interactively pick successor states when it
		// evaluates to FALSE.
		final Value guard = tool.eval(args[0], c, s0, s1, control, cm);
		if (!(guard instanceof BoolValue)) {
			Assert.fail("In evaluating TLCExt!PickSuccessor, a non-boolean expression (" + guard.getKindString()
					+ ") was used as the condition " + "of an IF.\n" + args[0]);
		}
		if (((BoolValue) guard).val) {
			return BoolValue.ValTrue;
		}

		if (s1 == TLCState.Empty || !s1.allAssigned()) {
			// Evaluates to TRUE if PickSuccessor is evaluated in the context of a
			// constant- or state-level formula such as a state-constraint or invariant.
			// Also evaluates to TRUE if PickSuccessor appears as part of the next-state
			// relation before all primed variables are defined.
			return BoolValue.ValTrue;
		}
		
		Action action = null;
		if (s1 instanceof TLCStateMutExt) {
			action = s1.getAction();
		} else {
			// Find the (first) Action this pair of states belongs to. If more than one
			// Action match, we pick the first one.
			// TODO: This is clumsy (we regenerate all next-states again) and incorrect if
			// two actions generate the same successor states. It's good enough for now
			// until the Action instance was passed down the call-stack.
			LOOP: for (Action act : tool.getActions()) {
				StateVec nextStates = tool.getNextStates(act, s0);
				if (nextStates.contains(s1)) {
					action = act;
					break LOOP;
				}
			}
		}

		while (true) {
			// TODO Add more commands such as continue/resume to pick every successor,
			// randomly pick next N successors, terminate to stop state space exploration,
			// ...
			MP.printMessage(EC.TLC_MODULE_OVERRIDE_STDOUT,
					String.format(
							"Extend behavior of length %s with a \"%s\" step [%s]? (Yes/no/explored/states/diff):",
							s0.getLevel(), action.getName(), action));

			final String nextLine = scanner.nextLine();
			if (nextLine.trim().isEmpty() || nextLine.toLowerCase().startsWith("y")) {
				return BoolValue.ValTrue;
			} else if (nextLine.charAt(0) == 's') {
				MP.printMessage(EC.TLC_MODULE_OVERRIDE_STDOUT,
						String.format("%s\n~>\n%s", s0.toString().trim(), s1.toString().trim()));
			} else if (nextLine.charAt(0) == 'd') {
				MP.printMessage(EC.TLC_MODULE_OVERRIDE_STDOUT, s1.toString(s0));
			} else if (nextLine.charAt(0) == 'e') {
				if (TLCGlobals.mainChecker != null) {
					try {
						((ModelChecker) TLCGlobals.mainChecker).theFPSet.put(s1.fingerPrint());
					} catch (IOException notExpectedToHappen) {
						notExpectedToHappen.printStackTrace();
					}
					return BoolValue.ValTrue;
				} else {
					MP.printMessage(EC.TLC_MODULE_OVERRIDE_STDOUT, String.format(
							"Marking a state explored is unsupported by the current TLC mode. Is TLC running in simulation mode?"));
				}
			} else if (nextLine.charAt(0) == 'n') {
				return BoolValue.ValFalse;
			}
		}
	}

	@TLAPlusOperator(identifier = "ToTrace", module = "TLCExt", warn = false)
	public static Value lassoOrdinal(final Value val) {
		if (!(val instanceof CounterExample)) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "ToTrace", "CounterExample", Values.ppr(val.toString()) });
		}
		return ((CounterExample) val).toTrace();
	}

	@Evaluation(definition = "CounterExample", module = "TLCExt", minLevel = 1, warn = false, silent = true)
	public static Value error(final Tool tool, final ExprOrOpArgNode[] args, final Context c,
			final TLCState s0, final TLCState s1, final int control, final CostModel cm) throws IOException {

		final Object lookup = c.lookup(tool.getCounterExampleDef());
		if (lookup instanceof Value) {
			return (Value) lookup;
		}
		// No CounterExample.
		return new CounterExample();
	}

	@Evaluation(definition = "Trace", module = "TLCExt", minLevel = 1, warn = false, silent = true)
	public static TupleValue getTrace(final Tool tool, final ExprOrOpArgNode[] args, final Context c,
			final TLCState s0, final TLCState s1, final int control, final CostModel cm) throws IOException {

		if (!s0.allAssigned()) {
			/*
			 * Fail when Trace appears before the state is completely specified (see
			 * EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL)
			 *
			 * VARIABLE var
			 * ...
			 * Init == PrintT(Trace) /\ var = 42
			 * ...
			 */
			final Set<OpDeclNode> unassigned = s0.getUnassigned();
			Assert.fail(EC.GENERAL, String.format(
					"In evaluating TLCExt!Trace, the state is not completely specified yet (variable%s %s undefined).",
					unassigned.size() > 1 ? "s" : "",
					unassigned.stream().map(n -> n.getName().toString()).collect(Collectors.joining(", "))));
		}

		if (TLCGlobals.simulator != null) {
			// TODO Somehow load only this implementation in simulation mode => module
			// overrides for a specific tool mode.
			final StateVec trace = TLCGlobals.simulator.getTrace(s0);
			
			final Value[] values = new Value[trace.size()];
			for (int j = 0; j < trace.size(); j++) {
				final TLCState state = trace.elementAt(j);
				values[j] = new RecordValue(state, state.getAction());
			}
			
			return new TupleValue(values);
		}
		
		if (s0.isInitial()) {
			return new TupleValue(new Value[] { new RecordValue(s0) });
		}
			
		synchronized (TLCExt.class) {
			if (s0.uid == TLCState.INIT_UID) {
				// The state s0 has not been written do disk, i.e. the trace file.
				// This is the case where Trace is evaluated in a state-constraint when the
				// trace up to s0 hasn't been constructed yet.  Consequently, we cannot 
				// re-construct the trace up to s0.  Instead, we re-construct the trace up
				// to s0's predecessor sP.  If sP is an initial state, we are done and return
				// the trace of length two.  Otherwise, we re-construct the trace to sP and
				// append sP and s0.
				// Obviously, this hack is prohibitively expensive if evaluated for every state.
				// However, the TLCDebugger makes use of this should a user manually request
				// the trace for a TLCStateStackFrame that correspond to a state-constraint.
				// For this use-case, we consider this good enough.
				//TODO: This won't work if TLCExt is extended to return action names for which
				// we have to create proper TLCStateInfo instances below instead of instantiating
				// them here.
				final List<TLCStateInfo> trace = new ArrayList<>();
				
				final TLCState currentState = IdThread.getCurrentState();
				if (currentState.isInitial()) {
					trace.add(new TLCStateInfo(currentState));
					trace.add(new TLCStateInfo(s0));
				} else {
					trace.addAll(Arrays.asList(TLCGlobals.mainChecker.getTraceInfo(currentState)));
					trace.add(new TLCStateInfo(currentState));
					trace.add(new TLCStateInfo(s0));
					// A side-effect of getTraceInfo are nested calls to setCurrentState. Thus, we
					// have to reset to currentState after we are done with our getTraceInfo business.
					IdThread.setCurrentState(currentState);
				}
				return new TupleValue(trace.stream().map(si -> new RecordValue(si.state)).toArray(Value[]::new));
			}
			return getTrace0(s0, TLCGlobals.mainChecker.getTraceInfo(s0));
		}
	}

	private static final TupleValue getTrace0(final TLCState s0, final TLCStateInfo[] trace) {
		final Value[] values = new Value[trace.length + 1];
		for (int j = 0; j < (trace.length); j++) {
			values[j] = new RecordValue(trace[j].state);
		}
		values[values.length - 1] = new RecordValue(s0);
		return new TupleValue(values);
	}

	@Evaluation(definition = "TLCDefer", module = "TLCExt", warn = false, silent = true)
	public static Value tlcDefer(final Tool tool, final ExprOrOpArgNode[] args, final Context c,
			final TLCState s0, final TLCState s1, final int control, final CostModel cm) {
		try {
			// We should compare control to EvalControl.Primed instead of setting the
			// callable on s0 and s1, but @Evaluation doesn't seem to correctly pass
			// control in all scopes such as the next-state relation, state-, and
			// action-constraints.  
			Stream.of(s0, s1).forEach(s -> s.setCallable(() -> {
				final Value[] argVals = new Value[args.length];
				// evaluate the operator's arguments:
				for (int i = 0; i < args.length; i++) {
					argVals[i] = tool.eval(args[i], c, s0, s1, control, cm);
				}
				return null;
			}));
		} catch (Throwable e) {
			Assert.fail(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[] { "TLCDefer", e.getMessage() });
		}
		return BoolValue.ValTrue;
	}

	@TLAPlusOperator(identifier = "TLCNoOp", module = "TLCExt", warn = false)
	public static Value tlcNoOp(final Value val) {
		return val;
	}

	@TLAPlusOperator(identifier = "TLCModelValue", module = "TLCExt", warn = false)
	public static synchronized Value tlcModelValue(final Value val) {
		if (!(val instanceof StringValue)) {
			throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR,
					new String[] { "ModelValue", "string", Values.ppr(val.toString()) });
		}
		final StringValue str = (StringValue) val;
		return ModelValue.add(str.val.toString());
	}
	
	@Evaluation(definition = "TLCCache", module = "TLCExt", warn = false, silent = true)
	public static Value tlcEval2(final Tool tool, final ExprOrOpArgNode[] args, final Context c, final TLCState s0,
			final TLCState s1, final int control, final CostModel cm) {

		final ExprOrOpArgNode expr = args[0];
		final ExprOrOpArgNode closure = args[1];

		if (expr.getLevel() == LevelConstants.VariableLevel) {

			final int key = expr.hashCode() ^ closure.hashCode() ^ tool.eval(closure, c, s0).hashCode();

			final Value value = s0.getCached(key);
			if (value != null) {
				return value;
			}

			return s0.setCached(key, tool.eval(expr, c, s0, s1, control, cm));
		}

		// For constant, action or temporal formulas, all we do is to evaluate the TLA+
		// expression--nothing is cached!
		return null; // Returning null here causes Tool.java to evaluate the original expression.
	}
}
