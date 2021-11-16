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
package tlc2.value.impl;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Comparator;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.OpDefNode;
import tlc2.output.EC;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import util.Assert;

public class PriorityEvaluatingValue extends EvaluatingValue {

	private static final Comparator<EvaluatingValue> comparator = new Comparator<EvaluatingValue>() {
		@Override
		public int compare(EvaluatingValue o1, EvaluatingValue o2) {
			return Integer.compare(o1.priority, o2.priority);
		}
	};

	private final ArrayList<EvaluatingValue> handles = new ArrayList<>();

	public PriorityEvaluatingValue(final Method md, final int minLevel, final int priority, final OpDefNode opDef,
			final EvaluatingValue ev) {
		super(md, minLevel, priority, opDef);
		if (ev.opDef != this.opDef || ev.minLevel != this.minLevel) {
			// TODO Specific error code.
			Assert.fail(EC.GENERAL);
		}

		this.handles.add(this);
		this.handles.add(ev);
		this.handles.sort(comparator);
	}

	public void add(EvaluatingValue ev) {
		if (ev.opDef != this.opDef || ev.minLevel != this.minLevel) {
			// TODO Specific error code.
			Assert.fail(EC.GENERAL);
		}
		this.handles.add(ev);
		this.handles.sort(comparator);
	}

	@Override
	public Value eval(final Tool tool, final ExprOrOpArgNode[] args, final Context c, final TLCState s0,
			final TLCState s1, final int control, final CostModel cm) {
		try {
			for (EvaluatingValue ev : handles) {
				final Object invoke = ev.mh.invoke(tool, args, c, s0, s1, control, cm);
				if (invoke != null) {
					return (Value) invoke;
				}
			}
			// Fall back to pure (TLA+) operator definition if the Java module overrides
			// returned null.
			return tool.eval(opDef.getBody(), c, s0, s1, control, cm);
		} catch (Throwable e) {
			Assert.fail(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE, new String[] { this.md.toString(), e.getMessage() });
			return null; // make compiler happy
		}
	}
}
