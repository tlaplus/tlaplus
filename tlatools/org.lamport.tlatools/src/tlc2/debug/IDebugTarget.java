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

import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.Action;
import tlc2.tool.INextStateFunctor;
import tlc2.tool.StatefulRuntimeException;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.Value;

public interface IDebugTarget {

	public enum StepDirection {
		/**
		 * Resume regular state-space exploration.
		 */
		Continue,
		/**
		 * Continue state-space exploration with the given state.
		 */
		In,
		/**
		 * Go back to the previous level/diameter.
		 */
		Out,
		/**
		 * Ignore the current state and continue with other successor states (if any).
		 */
		Over;
	}

	public enum Granularity {
		State, Formula
	};

	public enum Step {
		In, Out, Over, Continue, Reset, Reset_Start
	};

	@SuppressWarnings("serial")
	class ResetEvalException extends RuntimeException {
	
		public final TLCStackFrame frame;
		
		public ResetEvalException(TLCStackFrame frame) {
			assert frame != null;
			this.frame = frame;
		}

		public boolean isTarget(SemanticNode expr) {
			return frame.isTarget(expr);
		}
	}

	@SuppressWarnings("serial")
	class AbortEvalException extends RuntimeException {
		// Tool#getNextStates(..) does not support stopping the evaluation of the
		// next-state relation. In other words, it always generates all successor states
		// (unless running in probabilistic/generator mode). Here, however, we may want
		// to stop the evaluation of the next-state relation before all successors have
		// been generated. Thus, we throw an AbortEvalException that we catch further up
		// the call-stack (see above). We assume Tool to gracefully handle this
		// exception and correctly cleanup and reset for the next evaluation of the
		// next-state relation.
	}

	IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c);
	
	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c);
	
	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, Value v);

	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, TLCState state);

	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, Value v, TLCState state);

	IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c, TLCState state);

	IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c, TLCState predecessor, Action a, TLCState state);
	
	StepDirection pushFrame(Tool tool, OpDefNode expr, Context c, TLCState predecessor, Action a, INextStateFunctor fun);

	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, TLCState predecessor, TLCState state);

	IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, Value v, TLCState predecessor, TLCState state);

	IDebugTarget popExceptionFrame(Tool tool, SemanticNode expr, Context c, Value v, TLCState predecessor, TLCState state, StatefulRuntimeException e);

	IDebugTarget popFrame(Tool tool, OpDefNode expr, Context c, TLCState predecessor, Action a, INextStateFunctor fun);

	IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, StatefulRuntimeException e);
	
	IDebugTarget popExceptionFrame(Tool tool, SemanticNode expr, Context c, Value v, StatefulRuntimeException e);

	IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, TLCState state, StatefulRuntimeException e);

	IDebugTarget popExceptionFrame(Tool tool, SemanticNode expr, Context c, Value v, TLCState state, StatefulRuntimeException e);

	IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, TLCState predecessor, Action a, TLCState state,
			StatefulRuntimeException e);

	IDebugTarget popExceptionFrame(Tool tool, SemanticNode expr, Context c, TLCState predecessor, Action a, TLCState state,
			StatefulRuntimeException e);

	IDebugTarget markInvariantViolatedFrame(Tool debugTool, SemanticNode pred, Context c, TLCState predecessor, Action a, TLCState state, StatefulRuntimeException e);

	IDebugTarget markAssumptionViolatedFrame(Tool debugTool, SemanticNode pred, Context c);

	//------------------------ Wrapper --------------------------//
	
	IDebugTarget pushFrame(TLCState state);
	
	IDebugTarget popFrame(TLCState state);

	StepDirection pushFrame(TLCState predecessor, Action a, TLCState state);

	IDebugTarget popFrame(TLCState predecessor, TLCState state);

	IDebugTarget setTool(Tool tool);
}
