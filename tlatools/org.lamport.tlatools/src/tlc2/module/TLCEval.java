/*******************************************************************************
 * Copyright (c) 2022 Microsoft Research. All rights reserved.
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

import java.util.concurrent.locks.ReadWriteLock;
import java.util.concurrent.locks.ReentrantReadWriteLock;

import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.LevelConstants;
import tlc2.overrides.Evaluation;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.Tool;
import tlc2.tool.impl.WorkerValue;
import tlc2.util.Context;
import tlc2.value.ValueConstants;
import tlc2.value.impl.Value;

public class TLCEval implements ValueConstants {

	public static final long serialVersionUID = 20220105L;

	private static final ReadWriteLock lock = new ReentrantReadWriteLock();

	private static Value convert(final Value eval) {
		// Legacy implementation of TLCEval taken from TLC.java
		Value evalVal = eval.toSetEnum();
		if (evalVal != null) {
			return evalVal;
		}
		evalVal = eval.toFcnRcd();
		if (evalVal != null) {
			return evalVal;
		}
		return eval;
	}

	/**
	 * Implements TLCEval, which causes TLC to eagerly evaluate the value. Useful
	 * for preventing inefficiency caused by lazy evaluation defeating efforts at
	 * common subexpression elimination.
	 */
	@Evaluation(definition = "TLCEval", module = "TLC", warn = false, silent = true)
	public static Value tlcEval(final Tool tool, final ExprOrOpArgNode[] args, final Context c, final TLCState s0,
			final TLCState s1, final int control, final CostModel cm) {
		// TLCEval has a single parameter:
		final ExprOrOpArgNode arg = args[0];

		if (arg.getLevel() > LevelConstants.ConstantLevel) {
			// For a non-constant expression, all we can do is to evaluate
			// and convert the value according to the old implementation
			// of TLCEval.
			// Since there is no sharing going on, there is no need to deal
			// with WorkerValue here.
			
			// The value that a constant-level expression evaluates to is stored in the
			// semantic graph. 
			// For a state-level formula, the value could be kept in a transient member
			// of the state.  This effort doesn't seem worth it, though.
			return convert(tool.eval(arg, c, s0, s1, control, cm));
		} else if (!c.isDeepEmpty()) {
			// If a constant expression has a context, e.g. a parameter, we
			// cannot cache the value.
			return convert(tool.eval(arg, c, s0, s1, control, cm));
		}

		return tlcEvalConst(tool, arg, cm);
	}

	private static Value tlcEvalConst(Tool tool, ExprOrOpArgNode arg, CostModel cm) {
		assert arg.getLevel() == LevelConstants.ConstantLevel;
		
		lock.readLock().lock();

		// Read with ReadLock
		Object obj = WorkerValue.mux(arg.getToolObject(tool.getId()));
		if (obj != null) {
			// Return the cached value.
			try {
				return (Value) obj;
			} finally {
				lock.readLock().unlock();
			}
		}

		// Slow-path below. Note that ReentrantRWLock deadlocks when
		// upgrading a read to a write-lock, but we don't need this here.
		lock.readLock().unlock();

		lock.writeLock().lock();
		try {
			// Re-read with WriteLock in case another thread obtained
			// the write lock while this thread waited.
			obj = WorkerValue.mux(arg.getToolObject(tool.getId()));
			if (obj != null) {
				return (Value) obj;
			}

			// Create/Write the value!
			final Object demuxed =  WorkerValue.demux(tool, arg, cm);
			Value eval;
			if (demuxed instanceof Value) {
				eval = (Value) demuxed;
			} else {
				eval = (Value) WorkerValue.mux((WorkerValue) demuxed);
			}
			eval = convert(eval);
			arg.setToolObject(tool.getId(), eval);
			return eval;
		} finally {
			lock.writeLock().unlock();
		}
	}
}
