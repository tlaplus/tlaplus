/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.Variable;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.TLCGlobals;
import tlc2.tool.EvalException;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.TLCStateMutExt;
import tlc2.tool.impl.DebugTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.RecordValue;
import util.Assert.TLCRuntimeException;

public class TLCStateStackFrame extends TLCStackFrame {
	
	// A placeholder for the value of a variable that has not yet been evaluated.
	public static final String NOT_EVALUATED = "null";
	
	public static final String SCOPE = "State";

	public static final String TRACE = "Trace";

	protected transient final TLCState state;
	protected transient final int stateId;

	public TLCStateStackFrame(TLCStackFrame parent, SemanticNode node, Context ctxt, Tool tool, TLCState state) {
		this(parent, node, ctxt, tool, state, null);
	}

	public TLCStateStackFrame(TLCStackFrame parent, SemanticNode node, Context ctxt, Tool tool, TLCState state,
			RuntimeException e) {
		super(parent, node, ctxt, tool, e);
		this.state = state.deepCopy();
		assert this.state instanceof TLCStateMutExt;
		
		// Tempting to use state.fingerprint/hashCode, but would normalize all values as(
		// a side effect.
		this.stateId = rnd.nextInt(Integer.MAX_VALUE - 1) + 1;
	}
	
	protected TLCState getS() {
		return getT();
	}
	
	protected TLCState getT() {
		return state;
	}

	Variable[] getTrace() {
		return getVariables(stateId + 1);
	}

	@Override
	public Variable[] getVariables(int vr) {
		if (vr == stateId) {
			return tool.eval(() -> {
				return new Variable[] { toVariable() };
			});
		}
		if (vr == stateId + 1) {
			return ((DebugTool) tool).eval(() -> {
				try {
					// A) Last state of the trace s_f.
					final TLCState t = getT();
					
					if (t.getPredecessor() == null) {
						assert t.isInitial();
						// No need to re-construct a trace if this.state is an initial state. Note that
						// getTrace(s)/getTraceInfo(s) below would return a trace, but a check at the
						// beginning seems easier.
						return new Variable[] { getVariable(new RecordValue(t, NOT_EVALUATED), "1: <Initial predicate>") };
					}
					
					final Deque<Variable> trace = new ArrayDeque<>();
					trace.add(
							getVariable(new RecordValue(t, NOT_EVALUATED), t.getLevel() + ": " + t.getAction().getLocation()));

					final TLCStateInfo[] prefix;
					if (TLCGlobals.simulator != null) {
						prefix = TLCGlobals.simulator.getTraceInfo(t.getLevel() - 1);
					} else {
						// B) Suffix from s_f to either an initial state or a state whose predecessor
						// has to be looked up from disk (s_d).
						TLCState last = t;
						TLCState s = t;
						while ((s = s.getPredecessor()) != null) {
							if (s.isInitial()) {
								trace.add(getVariable(new RecordValue(s, NOT_EVALUATED), "1: <Initial predicate>"));
								return trace.toArray(new Variable[trace.size()]);
							}
							trace.add(getVariable(new RecordValue(s, NOT_EVALUATED),
									s.getLevel() + ": " + s.getAction().getLocation()));
							last = s;
						}
						
						// C) The prefix from an initial state s_i to the predecessor of s_d. We can
						// assert that s_d is no initial state, it will *not* be part of prefix.
						final List<TLCStateInfo> arrayList = new ArrayList<>(
								Arrays.asList(TLCGlobals.mainChecker.getTraceInfo(last)));
						prefix = arrayList.toArray(TLCStateInfo[]::new);
					}

					// Combine and convert the trace into debugger Variables. It's in
					// reverse order because the variable view shows the current state in the
					// "State" node (SCOPE) above Trace; if a user ignores the "State" and "Trace"
					// nodes, it almost reads like a regular trace.
					for (int i = prefix.length - 1; i >= 0; i--) {
						final TLCStateInfo ti = prefix[i];
						trace.add(getVariable(new RecordValue(ti.state),
								// The name of the variable has to be unique for all states to show up in the
								// variable view. Otherwise, the variable view will silently discard all but on
								// of the variable with the same name. Thus, we prepend the state number, which
								// also make it easier for users to understand how states are ordered.
								ti.state.getLevel() + ": " + ti.info.toString()));
					}
					
					return trace.toArray(new Variable[trace.size()]);
				} catch (IOException e) {
					//TODO: Handle exception case.
					return new Variable[0];
				}
			});
		}
		return super.getVariables(vr);
	}

	protected Variable toVariable() {
		return getVariable(toRecordValue(), getT().getLevel() + ": " + getActionName(getT()));
	}

	protected String getActionName(final TLCState state) {
		return state.getAction() == null ? "<Initial predicate>" : state.getAction().getLocation();
	}
	
	protected RecordValue toRecordValue() {
		return new RecordValue(getT(), NOT_EVALUATED);
	}

	Variable[] getStateVariables() {
		return getVariables(stateId);
	}

	@Override
	protected Variable getVariable(final LinkedList<SemanticNode> path) {
		assert !path.isEmpty();
		
		if (!isPrimeScope(path)) {
			SymbolNode var = tool.getVar(path.getFirst(), ctxt, false, tool.getId());
			if (var != null) {
				final IValue value = getS().lookup(var.getName());
				if (value != null) {
					return getVariable(value, var.getName());
				} else {
					Variable v = new Variable();
					v.setName(var.getName().toString());
					v.setValue(NOT_EVALUATED);
					return v;
				}
			}
		} else if (isPrimeScope(path)) {
			// TLCStateStackFrame implies that there is no successor state, probably because
			// the stack frame belongs to the evaluation of the initial predicate, an
			// invariant, a state-constraint...  In this scope, a primed variable has no value.
			final Variable variable = new Variable();
			variable.setName(path.getFirst().getHumanReadableImage());
			variable.setValue(path.getFirst().getLocation().toString());
			return variable;
		}
		return super.getVariable(path);
	}
	
	protected boolean isPrimeScope(LinkedList<SemanticNode> path) {
		for (SemanticNode semanticNode : path) {
			if (semanticNode instanceof OpApplNode) {
				OpApplNode oan = (OpApplNode) semanticNode;
				if (ASTConstants.OP_prime == oan.getOperator().getName()) {
					return true;
				}
			}
		}
		return false;
	}

	@Override
	public Scope[] getScopes() {
		final List<Scope> scopes = new ArrayList<>();
		scopes.addAll(Arrays.asList(super.getScopes()));
		
		// TODO: Consider merging SCOPE and TRACE. The separation, however, makes sure
		// that we only pay the price for re-constructing the error-trace if a user
		// actually expands the Trace node in the variable view, which I assume to
		// happen less often than expanding the current state (SCOPE).
		// Alternatively, we could cache the re-constructed trace while a user steps
		// through an action, i.e. while the trace doesn't change.  Traversing
		// up the TLCStackFrame stack is already implemented by
		// tlc2.debug.TLCStackFrame.getStackVariables(List<Variable>). For simulation,
		// we get the trace for free though.  There would be no need to cache it.
		Scope scope = new Scope();
		scope.setName(getScope());
		scope.setVariablesReference(stateId);
		scopes.add(scope);
		
		scope = new Scope();
		scope.setName(TRACE);
		scope.setVariablesReference(stateId + 1);
		scopes.add(scope);
		
		return scopes.toArray(new Scope[scopes.size()]);
	}

	protected String getScope() {
		return SCOPE;
	}

	@Override
	protected Object unlazy(LazyValue lv) {
		return unlazy(lv, null);
	}
	
	@Override
	protected Object unlazy(final LazyValue lv, final Object fallback) {
		try {
			return tool.eval(() -> {
				return lv.eval(tool, getS());
			});
		} catch (TLCRuntimeException | EvalException e) {
			return fallback == null ? e : fallback;
		}
	}

	@Override
	public boolean matches(final TLCSourceBreakpoint bp) {
		if (super.matches(bp)) {
			if (bp.getHits() > 0) {
				// TODO: getLast here to have uniform hit count for actions an their
				// state-constraint.
				return getT().getLevel() >= bp.getHits(); 
			}
			return true;
		}
		return false;
	}
}
