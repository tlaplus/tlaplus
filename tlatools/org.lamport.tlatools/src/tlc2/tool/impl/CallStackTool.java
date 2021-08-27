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
package tlc2.tool.impl;

import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.Action;
import tlc2.tool.CallStack;
import tlc2.tool.EvalException;
import tlc2.tool.FingerprintException;
import tlc2.tool.IActionItemList;
import tlc2.tool.INextStateFunctor;
import tlc2.tool.IStateFunctor;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.value.impl.FcnLambdaValue;
import tlc2.value.impl.OpLambdaValue;
import tlc2.value.impl.SetPredValue;
import tlc2.value.impl.Value;
import util.Assert.TLCRuntimeException;

public final class CallStackTool extends Tool {

	private final CallStack callStack = new CallStack();

	public CallStackTool(ITool other) {
		super((Tool) other);
	}

	@Override
	public final String toString() {
		return this.callStack.toString();
	}

	@Override
	protected final void getInitStates(final SemanticNode init, final ActionItemList acts, final Context c,
			final TLCState ps, final IStateFunctor states, final CostModel cm) {
		this.callStack.push(init);
		try {
			super.getInitStates(init, acts, c, ps, states, cm);
		} catch (TLCRuntimeException | EvalException e) {
			// Freeze the callStack to ignore subsequent pop operations. This is
			// necessary to ignore the callStack#pop calls in the finally blocks when the
			// Java call stack gets unwounded.
			this.callStack.freeze();
			throw e;
		} catch (FingerprintException e) {
			this.callStack.freeze(e);
			throw e;
		} finally {
			this.callStack.pop();
		}
	}

	protected void getInitStatesAppl(final OpApplNode init, final ActionItemList acts, final Context c,
			final TLCState ps, final IStateFunctor states, final CostModel cm) {
		this.callStack.push(init);
		try {
			super.getInitStatesAppl(init, acts, c, ps, states, cm);
		} catch (TLCRuntimeException | EvalException e) {
			// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context,
			// TLCState, IStateFunctor)
			this.callStack.freeze();
			throw e;
		} catch (FingerprintException e) {
			this.callStack.freeze(e);
			throw e;
		} finally {
			this.callStack.pop();
		}
	}

	@Override
	protected final TLCState getNextStates(final Action action, final SemanticNode pred, final ActionItemList acts,
			final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
		this.callStack.push(pred);
		try {
			return getNextStatesImpl(action, pred, acts, c, s0, s1, nss, cm);
		} catch (TLCRuntimeException | EvalException e) {
			// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context,
			// TLCState, IStateFunctor)
			this.callStack.freeze();
			throw e;
		} catch (FingerprintException e) {
			this.callStack.freeze(e);
			throw e;
		} finally {
			this.callStack.pop();
		}
	}

	@Override
	protected final TLCState getNextStatesAppl(final Action action, final OpApplNode pred, final ActionItemList acts,
			final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
		this.callStack.push(pred);
		try {
			return getNextStatesApplImpl(action, pred, acts, c, s0, s1, nss, cm);
		} catch (TLCRuntimeException | EvalException e) {
			// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context,
			// TLCState, IStateFunctor)
			this.callStack.freeze();
			throw e;
		} catch (FingerprintException e) {
			this.callStack.freeze(e);
			throw e;
		} finally {
			this.callStack.pop();
		}
	}

	@Override
	public final Value eval(final SemanticNode expr, final Context c, final TLCState s0, final TLCState s1,
			final int control, final CostModel cm) {
		this.callStack.push(expr);
		try {
			// Replace stale ITool instances with this instance.
			final Value value = evalImpl(expr, c, s0, s1, control, cm);
			if (value instanceof SetPredValue) {
				return new SetPredValue((SetPredValue) value, this);
			} else if (value instanceof FcnLambdaValue) {
				return new FcnLambdaValue((FcnLambdaValue) value, this);
			} else if (value instanceof OpLambdaValue) {
				return new OpLambdaValue((OpLambdaValue) value, this);
			}
			return value;
		} catch (TLCRuntimeException | EvalException e) {
			// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context,
			// TLCState, IStateFunctor)
			this.callStack.freeze();
			throw e;
		} catch (FingerprintException e) {
			this.callStack.freeze(e);
			throw e;
		} finally {
			this.callStack.pop();
		}
	}

	@Override
	protected final Value evalAppl(final OpApplNode expr, final Context c, final TLCState s0, final TLCState s1,
			final int control, final CostModel cm) {
		this.callStack.push(expr);
		try {
			// Replace stale ITool instances with this instance.
			final Value value = evalApplImpl(expr, c, s0, s1, control, cm);
			if (value instanceof SetPredValue) {
				return new SetPredValue((SetPredValue) value, this);
			} else if (value instanceof FcnLambdaValue) {
				return new FcnLambdaValue((FcnLambdaValue) value, this);
			} else if (value instanceof OpLambdaValue) {
				return new OpLambdaValue((OpLambdaValue) value, this);
			}
			return value;
		} catch (TLCRuntimeException | EvalException e) {
			// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context,
			// TLCState, IStateFunctor)
			this.callStack.freeze();
			throw e;
		} catch (FingerprintException e) {
			this.callStack.freeze(e);
			throw e;
		} finally {
			this.callStack.pop();
		}
	}

	@Override
	public final TLCState enabled(final SemanticNode pred, final IActionItemList acts, final Context c,
			final TLCState s0, final TLCState s1, final CostModel cm) {
		this.callStack.push(pred);
		try {
			return enabledImpl(pred, (ActionItemList) acts, c, s0, s1, cm);
		} catch (TLCRuntimeException | EvalException e) {
			// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context,
			// TLCState, IStateFunctor)
			this.callStack.freeze();
			throw e;
		} catch (FingerprintException e) {
			this.callStack.freeze(e);
			throw e;
		} finally {
			this.callStack.pop();
		}
	}

	@Override
	protected final TLCState enabledAppl(final OpApplNode pred, final ActionItemList acts, final Context c,
			final TLCState s0, final TLCState s1, CostModel cm) {
		this.callStack.push(pred);
		try {
			return enabledApplImpl(pred, acts, c, s0, s1, cm);
		} catch (TLCRuntimeException | EvalException e) {
			// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context,
			// TLCState, IStateFunctor)
			this.callStack.freeze();
			throw e;
		} catch (FingerprintException e) {
			this.callStack.freeze(e);
			throw e;
		} finally {
			this.callStack.pop();
		}
	}

	@Override
	protected final TLCState processUnchanged(final Action action, final SemanticNode expr, final ActionItemList acts,
			final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, CostModel cm) {
		this.callStack.push(expr);
		try {
			return processUnchangedImpl(action, expr, acts, c, s0, s1, nss, cm);
		} catch (TLCRuntimeException | EvalException e) {
			// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context,
			// TLCState, IStateFunctor)
			this.callStack.freeze();
			throw e;
		} catch (FingerprintException e) {
			this.callStack.freeze(e);
			throw e;
		} finally {
			this.callStack.pop();
		}
	}

	@Override
	protected final TLCState enabledUnchanged(final SemanticNode expr, final ActionItemList acts, final Context c,
			final TLCState s0, final TLCState s1, final CostModel cm) {
		this.callStack.push(expr);
		try {
			return enabledUnchangedImpl(expr, acts, c, s0, s1, cm);
		} catch (TLCRuntimeException | EvalException e) {
			// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context,
			// TLCState, IStateFunctor)
			this.callStack.freeze();
			throw e;
		} catch (FingerprintException e) {
			this.callStack.freeze(e);
			throw e;
		} finally {
			this.callStack.pop();
		}
	}

	@Override
	protected final Value setSource(final SemanticNode expr, final Value value) {
		value.setSource(expr);
		return value;
	}

	public boolean hasCallStack() {
		return callStack.size() > 0;
	}
}
