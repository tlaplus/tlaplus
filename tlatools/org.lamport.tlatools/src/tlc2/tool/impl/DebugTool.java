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
package tlc2.tool.impl;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tlc2.debug.IDebugTarget;
import tlc2.tool.Action;
import tlc2.tool.EvalControl;
import tlc2.tool.IActionItemList;
import tlc2.tool.INextStateFunctor;
import tlc2.tool.IStateFunctor;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.value.impl.Value;
import util.FilenameToStream;

@SuppressWarnings("serial")
public class DebugTool extends Tool {

	private static final Set<Integer> KINDS = new HashSet<>(
			Arrays.asList(ASTConstants.NumeralKind, ASTConstants.DecimalKind, ASTConstants.StringKind));
	
	private final IDebugTarget target;

	public DebugTool(String mainFile, String configFile, FilenameToStream resolver, IDebugTarget target) {
		super(mainFile, configFile, resolver);
		this.target = target;
	}

	@Override
	public final Value eval(final SemanticNode expr, final Context c, final TLCState s0, final TLCState s1,
			final int control, final CostModel cm) {
		return evalImpl(expr, c, s0, s1, control, cm);
	}

	@Override
	protected Value evalImpl(final SemanticNode expr, final Context c, final TLCState s0, final TLCState s1,
			final int control, CostModel cm) {
		if (EvalControl.isDebug(control)) {
			// Skip debugging when evaluation was triggered by the debugger itself. For
			// example, when LazyValues get unlazied.
			return super.evalImpl(expr, c, s0, s1, control, cm);
		}
		if (KINDS.contains(expr.getKind())) {
			// These nodes don't seem interesting to users. They are leaves and we don't
			// care to see how TLC figures out that then token 1 evaluates to the IntValue 1.
			return super.evalImpl(expr, c, s0, s1, control, cm);
		}
		if (expr.getChildren() == null || expr.getChildren().length == 0) {
			// Skips N and Nat in:
			//     CONSTANT N
			//     ASSUME N \in Nat
			// or the S, the f, and the 1..3 of:
			//     LET FS == INSTANCE FiniteSets
	        //              Perms(S, a, b) == 
	        //                { f \in [S -> S] :
	        //                      /\ S = { f[x] : x \in DOMAIN f }
	        //                      /\ \E n, m \in DOMAIN f: /\ f[n] = a
	        //                                  /\ f[m] = b
	        //                                  /\ n - m \in {1, -1}               
	        //                }
	        //     IN FS!Cardinality(Perms(1..3, 1, 2)) = 4
			return super.evalImpl(expr, c, s0, s1, control, cm);
		}
//		if (c.isEmpty()) {
//			// It is tempting to ignore also frames with an empty Context. However, ASSUMES
//			// for example don't have a Context. Perhaps, we should track the level here and
//			// ignore frames with empty Context for level greater than zero (or whatever the
//			// base-level is).
//			return super.evalImpl(expr, c, s0, s1, control, cm);
//		}
		// target is null during instantiation of super, ie. eager evaluation of
		// operators in SpecProcessor.
		if (target != null) target.pushFrame(this, expr, c, s0, s1);
		final Value v = super.evalImpl(expr, c, s0, s1, control, cm);
		if (target != null) target.popFrame(this, expr, c, s0, s1);
		return v;
	}

	@Override
	protected final Value evalAppl(final OpApplNode expr, final Context c, final TLCState s0, final TLCState s1,
			final int control, final CostModel cm) {
		return evalApplImpl(expr, c, s0, s1, control, cm);
	}

	@Override
	protected final Value setSource(final SemanticNode expr, final Value value) {
		value.setSource(expr);
		return value;
	}

	@Override
	public final TLCState enabled(final SemanticNode pred, final IActionItemList acts, final Context c,
			final TLCState s0, final TLCState s1, final CostModel cm) {
		return enabledImpl(pred, (ActionItemList) acts, c, s0, s1, cm);
	}

	@Override
	protected final TLCState enabledAppl(final OpApplNode pred, final ActionItemList acts, final Context c,
			final TLCState s0, final TLCState s1, final CostModel cm) {
		return enabledApplImpl(pred, acts, c, s0, s1, cm);
	}

	@Override
	protected final TLCState enabledUnchanged(final SemanticNode expr, final ActionItemList acts, final Context c,
			final TLCState s0, final TLCState s1, final CostModel cm) {
		return enabledUnchangedImpl(expr, acts, c, s0, s1, cm);
	}

	@Override
	protected final TLCState getNextStates(final Action action, final SemanticNode pred, final ActionItemList acts,
			final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
		return getNextStatesImpl(action, pred, acts, c, s0, s1, nss, cm);
	}

	@Override
	protected final TLCState getNextStatesAppl(final Action action, final OpApplNode pred, final ActionItemList acts,
			final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
		target.pushFrame(this, pred, c, s0, s1);
		TLCState s = getNextStatesApplImpl(action, pred, acts, c, s0, s1, nss, cm);
		target.popFrame(this, pred, c, s0, s1);
		return s;
	}

	@Override
	protected final TLCState processUnchanged(final Action action, final SemanticNode expr, final ActionItemList acts,
			final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
		return processUnchangedImpl(action, expr, acts, c, s0, s1, nss, cm);
	}

	@Override
	protected void getInitStates(SemanticNode init, ActionItemList acts, Context c, TLCState ps, IStateFunctor states,
			CostModel cm) {
		if (states instanceof WrapperStateFunctor) {
			// Wrap the IStateFunctor so we can intercept Tool adding a new state to the
			// functor. Without it, the debugger wouldn't show the fully assigned state and
			// the variable that is assigned last will always be null.
			super.getInitStates(init, acts, c, ps, states, cm);
		} else {
			super.getInitStates(init, acts, c, ps, new WrapperStateFunctor(states, target), cm);
		}
	}
		
	@Override
	protected void getInitStatesAppl(OpApplNode init, ActionItemList acts, Context c, TLCState ps, IStateFunctor states,
			CostModel cm) {
		target.pushFrame(this, init, c, ps);
		super.getInitStatesAppl(init, acts, c, ps, states, cm);
		target.popFrame(this, init, c, ps);
	}

	@Override
	public boolean getNextStates(final INextStateFunctor functor, final TLCState state) {
		if (functor instanceof WrapperNextStateFunctor) {
			return super.getNextStates(functor, state);
		} else {
			return super.getNextStates(new WrapperNextStateFunctor(functor, target), state);
		}
	}
	
	private static class WrapperStateFunctor implements IStateFunctor {
		protected final IStateFunctor functor;
		protected final IDebugTarget target;

		WrapperStateFunctor(IStateFunctor functor, IDebugTarget target) {
			this.functor = functor;
			this.target = target;
		}
		
		@Override
		public Object addElement(TLCState state) {
			target.pushFrame(state);
			Object addElement = functor.addElement(state);
			target.popFrame(state);
			return addElement;
		}
	}

	private static class WrapperNextStateFunctor extends WrapperStateFunctor implements INextStateFunctor {

		WrapperNextStateFunctor(INextStateFunctor functor, IDebugTarget target) {
			super(functor, target);
		}

		@Override
		public Object addElement(TLCState predecessor, Action a, TLCState state) {
			target.pushFrame(predecessor, state);
			Object addElement = ((INextStateFunctor) functor).addElement(predecessor, a, state);
			target.popFrame(predecessor, state);
			return addElement;
		}
	}
}
