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
package tlc2.debug;

import tla2sany.semantic.SemanticNode;
import tlc2.debug.IDebugTarget.StepDirection;
import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;

public final class TLCStepActionStackFrame extends TLCActionStackFrame {

	private StepDirection step = StepDirection.Continue;

	public TLCStepActionStackFrame(TLCStackFrame f, SemanticNode node, Context context, Tool tool, TLCState s, Action a,
			TLCState t) {
		super(f, node, context, tool, s, a, t);
	}

	public void continue_() {
		this.step = StepDirection.Continue;
	}

	public void stepOver() {
		this.step = StepDirection.Over;
	}

	public void stepOut() {
		this.step = StepDirection.Out;
	}

	public void stepIn() {
		this.step = StepDirection.In;
	}

	public StepDirection getStepDirection() {
		return step;
	}
}
