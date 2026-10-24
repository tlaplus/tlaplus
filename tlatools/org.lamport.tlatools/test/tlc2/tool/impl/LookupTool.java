/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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
package tlc2.tool.impl;

import java.lang.reflect.Field;

import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.Action;
import tlc2.tool.IActionItemList;
import tlc2.tool.INextStateFunctor;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.value.impl.Value;
import util.UniqueString;

/**
 * A Tool that evaluates every expression to the value of one variable in the
 * current state, and supports nothing else.
 */
public final class LookupTool extends Tool {

	private UniqueString var;

	/**
	 * Every constructor of Tool parses a spec, so create skips the constructors,
	 * leaving the fields of Tool and Spec unset.
	 */
	public static Tool create(final UniqueString var) {
		try {
			final Field f = sun.misc.Unsafe.class.getDeclaredField("theUnsafe");
			f.setAccessible(true);
			final LookupTool tool = (LookupTool) ((sun.misc.Unsafe) f.get(null)).allocateInstance(LookupTool.class);
			tool.var = var;
			return tool;
		} catch (ReflectiveOperationException e) {
			throw new IllegalStateException(e);
		}
	}

	private LookupTool() {
		super((Tool) null);
	}

	@Override
	public Value eval(SemanticNode expr, Context c, TLCState s0, TLCState s1, int control, CostModel cm) {
		return (Value) s0.lookup(var);
	}

	@Override
	protected TLCState getNextStates(Action action, SemanticNode pred, ActionItemList acts, Context c, TLCState s0,
			TLCState s1, INextStateFunctor nss, CostModel cm) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected TLCState getNextStatesAppl(Action action, OpApplNode pred, ActionItemList acts, Context c, TLCState s0,
			TLCState s1, INextStateFunctor nss, CostModel cm) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected TLCState processUnchanged(Action action, SemanticNode expr, ActionItemList acts, Context c,
			TLCState s0, TLCState s1, INextStateFunctor nss, CostModel cm) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected Value evalAppl(OpApplNode expr, Context c, TLCState s0, TLCState s1, int control, CostModel cm) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected Value setSource(SemanticNode expr, Value value) {
		throw new UnsupportedOperationException();
	}

	@Override
	public TLCState enabled(SemanticNode pred, IActionItemList acts, Context c, TLCState s0, TLCState s1,
			CostModel cm) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected TLCState enabledAppl(OpApplNode pred, ActionItemList acts, Context c, TLCState s0, TLCState s1,
			CostModel cm) {
		throw new UnsupportedOperationException();
	}

	@Override
	protected TLCState enabledUnchanged(SemanticNode expr, ActionItemList acts, Context c, TLCState s0,
			TLCState s1, CostModel cm) {
		throw new UnsupportedOperationException();
	}
}
