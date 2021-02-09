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

import java.util.List;

import org.eclipse.lsp4j.debug.Variable;

import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.tool.EvalException;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.LazyValue;
import util.Assert.TLCRuntimeException;

public class TLCActionStackFrame extends TLCStateStackFrame {
	
	protected final TLCState succecessor;

	public TLCActionStackFrame(SemanticNode expr, Context c, Tool tool, TLCState predecessor, TLCState ps) {
		this(expr, c , tool, predecessor, ps, null);
	}
	
	public TLCActionStackFrame(SemanticNode expr, Context c, Tool tool, TLCState predecessor, TLCState ps, RuntimeException e) {
		super(expr, c , tool, predecessor, e);
		this.succecessor = ps.deepCopy();
	}

	@Override
	public Variable[] getVariables(int vr) {
		if (vr == stateId) {
			return tool.eval(() -> {
				final List<Variable> vars = getStateVariables(succecessor, "'");
				vars.addAll(getStateVariables(state, ""));
				return toSortedArray(vars);
			});
		}
		return super.getVariables(vr);
	}

	@Override
	protected Variable getVariable(Location location, final String symbol) {
		final SemanticNode sn = tool.getSpecProcessor().getNodeAt(location, symbol);
		if (isPrimed(sn)) {
			final IValue value = succecessor.lookup(symbol);
			if (value != null) {
				return getVariable(value, symbol + "'");
			}
		}
		return super.getVariable(location, symbol);
	}

	private boolean isPrimed(SemanticNode sn) {
		return tool.getPrimedVar(sn, ctxt, false) != null;
	}

	protected Object unlazy(final LazyValue lv) {
		return tool.eval(() -> {
			try {
				return lv.eval(tool, state, succecessor);
			} catch (TLCRuntimeException | EvalException e) {
				return e;
			}
		});
	}
}
