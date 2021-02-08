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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.Variable;

import tla2sany.semantic.SemanticNode;
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
	
	public static final String SCOPE = "State";

	protected transient final TLCState state;
	protected transient final int stateId;

	public TLCStateStackFrame(SemanticNode node, Context ctxt, Tool tool, TLCState state) {
		this(node, ctxt, tool, state, null);
	}
	
	public TLCStateStackFrame(SemanticNode node, Context ctxt, Tool tool, TLCState state, RuntimeException e) {
		super(node, ctxt, tool, e);
		this.state = state.deepCopy();
		
		// Tempting to use state.fingerprint/hashCode, but would normalize all values as a side effect.
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
				variable.setValue("null");
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
		
		final Scope scope = new Scope();
		scope.setName(SCOPE);
		scope.setVariablesReference(stateId);
		scopes.add(scope);
		
		return scopes.toArray(new Scope[scopes.size()]);
	}

	@Override
	protected Object unlazy(LazyValue lv) {
		try {
			return tool.eval(() -> {
				return lv.eval(tool, state);
			});
		} catch (TLCRuntimeException | EvalException e) {
			return e;
		}
	}
}
