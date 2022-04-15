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

import java.util.LinkedList;

import org.eclipse.lsp4j.debug.Variable;

import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.Action;
import tlc2.tool.EvalException;
import tlc2.tool.FingerprintException;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.IValue;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.RecordValue;
import util.Assert.TLCRuntimeException;

public class TLCActionStackFrame extends TLCStateStackFrame {
	
	public static final String SCOPE = "Action";

	@Override
	protected String getScope() {
		return SCOPE;
	}

	public TLCActionStackFrame(TLCStackFrame parent, SemanticNode expr, Context c, Tool tool, TLCState predecessor,
			Action a, TLCState ps) {
		this(parent, expr, c, tool, predecessor, a, ps, null);
	}

	public TLCActionStackFrame(TLCStackFrame parent, SemanticNode expr, Context c, Tool tool, TLCState predecessor,
			Action a, TLCState ps, RuntimeException e) {
		super(parent, expr, c, tool, ps /* super calls ps.deepCopy() */, e);
		assert predecessor != null;
		assert a != null;
		assert ps != null;
		// either ps is a stuttering state or has a predecessor.
		assert predecessor.getLevel() == ps.getLevel() || ps.getPredecessor() != null;
		// We *cannot* assert allAssigned here cause the check if ps is a good state (Tool#isGoodState) happens later.
//		assert predecessor.allAssigned();
//		assert ps.getPredecessor().allAssigned();
	}
	
	@Override
	protected TLCState getS() {
		return state.getPredecessor();
	}
	
	@Override
	protected TLCState getT() {
		return state;
	}
	
	@Override
	protected RecordValue toRecordValue() {
		return new RecordValue(getS(), getT(), NOT_EVAL);
	}

	@Override
	protected Variable getVariable(final LinkedList<SemanticNode> path) {
		assert !path.isEmpty();
		
		if (isPrimeScope(path)) {
			// No need to call getPrimedVar because sn.getFirst is the child of the
			// OpApplNode that represents the prime.
			final SymbolNode var = tool.getPrimedVar(path.getFirst(), ctxt, false);
			if (var != null) {
				final IValue value = getT().lookup(var.getName());
				if (value != null) {
					return getVariable(value, var.getName() + "'");
				} else {
					Variable v = new Variable();
					v.setName(var.getName() + "'");
					v.setValue(DebuggerValue.NOT_EVALUATED);
					return v;
				}
			}
		}
		return super.getVariable(path);
	}

	@Override
	protected Object unlazy(final LazyValue lv) {
		return unlazy(lv, null);
	}
	
	@Override
	protected Object unlazy(final LazyValue lv, final Object fallback) {
		return tool.eval(() -> {
			try {
				return lv.eval(tool, getS(), getT());
			} catch (TLCRuntimeException | EvalException | FingerprintException e) {
				return fallback == null ? e : fallback;
			}
		});
	}
}
