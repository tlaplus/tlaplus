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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.Variable;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.EvalException;
import tlc2.tool.TLCState;
import tlc2.tool.impl.DebugTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.LazyValue;
import util.Assert.TLCRuntimeException;
import util.UniqueString;

public class TLCStateStackFrame extends TLCStackFrame {
	
	// A placeholder for the value of a variable that has not yet been evaluated.
	public static final String NOT_EVALUATED = "null";
	
	public static final String SCOPE = "State";

	protected transient final TLCState state;
	protected transient final int stateId;

	public TLCStateStackFrame(TLCStackFrame parent, SemanticNode node, Context ctxt, Tool tool, TLCState state) {
		this(parent, node, ctxt, tool, state, null);
	}

	public TLCStateStackFrame(TLCStackFrame parent, SemanticNode node, Context ctxt, Tool tool, TLCState state,
			RuntimeException e) {
		super(parent, node, ctxt, tool, e);
		this.state = state.deepCopy();

		// Tempting to use state.fingerprint/hashCode, but would normalize all values as
		// a side effect.
		this.stateId = rnd.nextInt(Integer.MAX_VALUE - 1) + 1;
	}

	@Override
	public Variable[] getVariables(int vr) {
		if (vr == stateId) {
			return ((DebugTool) tool).eval(() -> {
				return getStateVariables(state);
			});
		}
		return super.getVariables(vr);
	}
	
	@Override
	protected Variable getVariable(final LinkedList<SemanticNode> path) {
		assert !path.isEmpty();
		
		if (!isPrimeScope(path)) {
			SymbolNode var = tool.getVar(path.getFirst(), ctxt, false, tool.getId());
			if (var != null) {
				final IValue value = state.lookup(var.getName());
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

	protected Variable[] getStateVariables(final TLCState state) {
		return toSortedArray(getStateVariables(state, ""));
	}

	protected List<Variable> getStateVariables(final TLCState state, final String prime) {
		final List<Variable> vars = new ArrayList<>();
		final Map<UniqueString, IValue> vals = state.getVals();
		for (final Entry<UniqueString, IValue> e : vals.entrySet()) {
			final UniqueString key = e.getKey();
			final IValue value = e.getValue();
			final DebugTLCVariable variable;
			if (value == null) {
				variable = new DebugTLCVariable(key.toString() + prime);
				variable.setValue(NOT_EVALUATED);
			} else {
				variable = (DebugTLCVariable) value
						.toTLCVariable(new DebugTLCVariable(key.toString() + prime), rnd);
				nestedVariables.put(variable.getVariablesReference(), variable);
			}
			vars.add(variable);
		}
		return vars;
	}

	@Override
	public Scope[] getScopes() {
		final List<Scope> scopes = new ArrayList<>();
		scopes.addAll(Arrays.asList(super.getScopes()));
		
		Scope scope = new Scope();
		scope.setName(SCOPE);
		scope.setVariablesReference(stateId);
		scopes.add(scope);
		
		return scopes.toArray(new Scope[scopes.size()]);
	}

	@Override
	protected Object unlazy(LazyValue lv) {
		return unlazy(lv, null);
	}
	
	@Override
	protected Object unlazy(final LazyValue lv, final Object fallback) {
		try {
			return tool.eval(() -> {
				return lv.eval(tool, state);
			});
		} catch (TLCRuntimeException | EvalException e) {
			return fallback == null ? e : fallback;
		}
	}

	@Override
	public boolean matches(final TLCSourceBreakpoint bp) {
		if (super.matches(bp)) {
			if (bp.getHits() > 0) {
				return state.getLevel() >= bp.getHits(); 
			}
			return true;
		}
		return false;
	}
}
