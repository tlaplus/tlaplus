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

import org.eclipse.lsp4j.debug.Capabilities;

import tla2sany.st.Location;
import tlc2.debug.IDebugTarget.Granularity;
import tlc2.debug.IDebugTarget.StepDirection;
import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.tool.impl.Tool.Mode;

public final class TLCStepActionStackFrame extends TLCActionStackFrame {

	private StepDirection step = StepDirection.Continue;

	public TLCStepActionStackFrame(TLCStackFrame f, Tool tool, TLCState s, Action a, TLCState t) {
		super(f, f.getNode(), f.getContext(), tool, s, a, t);
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

	@Override
	public boolean matches(final TLCSourceBreakpoint bp) {
		if (tool.getMode() == Mode.Simulation) {
			final Action nextPred = tool.getSpecProcessor().getNextPred();
			final Location loc = nextPred.getDefinition();
			if (loc.includes(bp.getLocation())) {
				return true;
			}
		}
		return false;
	}

	@Override
	public void preHalt(final TLCDebugger debugger) {
		debugger.sendCapabilities(TLCCapabilities.NO_STEP_BACK);
		debugger.setGranularity(Granularity.State);
	}

	@Override
	public void postHalt(final TLCDebugger debugger) {
		debugger.sendCapabilities(TLCCapabilities.STEP_BACK);
		debugger.setGranularity(Granularity.Formula);
	}

	private static class TLCCapabilities extends Capabilities {

		public static final Capabilities STEP_BACK = new TLCCapabilities(true);
		
		public static final Capabilities NO_STEP_BACK = new TLCCapabilities(false);

		public TLCCapabilities(boolean reverse) {
			super();
			setSupportsStepBack(reverse);
		}
	}
}
