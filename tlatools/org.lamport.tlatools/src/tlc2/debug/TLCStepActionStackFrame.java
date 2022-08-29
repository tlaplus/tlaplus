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
import org.eclipse.lsp4j.debug.ContinueResponse;
import tla2sany.st.Location;
import tlc2.debug.IDebugTarget.Granularity;
import tlc2.debug.IDebugTarget.StepDirection;
import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.tool.impl.Tool.Mode;

import java.util.concurrent.CompletableFuture;

public final class TLCStepActionStackFrame extends TLCActionStackFrame {

    private StepDirection step = StepDirection.Continue;

    public TLCStepActionStackFrame(final TLCStackFrame f, final Tool tool, final TLCState s, final Action a, final TLCState t) {
        super(f, f.getNode(), f.getContext(), tool, s, a, t);
    }

    @Override
    public boolean handle(final TLCDebugger debugger) {
        if (tool.getMode() != Mode.Simulation) {
            // State-level stepping only supported in simulation mode.
            return false;
        }
        return debugger.getGranularity() == Granularity.State;
    }

    @Override
    public CompletableFuture<ContinueResponse> continue_(final TLCDebugger debugger) {
        this.step = StepDirection.Continue;

        // Hitting continue in the front-end is how users reset the stepping granularity
        // back to Formula.
        debugger.setGranularity(Granularity.Formula);
        debugger.notify();
        return CompletableFuture.completedFuture(new ContinueResponse());
    }

    @Override
    public CompletableFuture<Void> stepOver(final TLCDebugger debugger) {
        this.step = StepDirection.Over;

        debugger.setGranularity(Granularity.Formula);
        debugger.notify();
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> stepOut(final TLCDebugger debugger) {
        this.step = StepDirection.Out;

        debugger.setGranularity(Granularity.Formula);
        debugger.notify();
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> stepIn(final TLCDebugger debugger) {
        this.step = StepDirection.In;

        debugger.setGranularity(Granularity.Formula);
        debugger.notify();
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> reverseContinue(final TLCDebugger debugger) {
        // Because we change the backend's capabilities when switching to state-level
        // stepping granularity (find setCapabilities in this class), the button mapping
        // to this method reverseContinue should not be available in the UI. To
        // safeguard against a deadlock, we simply define the buttons behavior to resume
        // execution.
        debugger.setGranularity(Granularity.Formula);
        debugger.notify();
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> stepBack(final TLCDebugger debugger) {
        // Because we change the backend's capabilities when switching to state-level
        // stepping granularity (find setCapabilities in this class), the button should
        // not be available in the UI. To safeguard against a deadlock, we simply define
        // the buttons behavior to resume execution.
        debugger.setGranularity(Granularity.Formula);
        debugger.notify();
        return CompletableFuture.completedFuture(null);
    }

    public StepDirection getStepDirection() {
        return step;
    }

    @Override
    public boolean matches(final TLCSourceBreakpoint bp) {
        if (tool.getMode() == Mode.Simulation) {
            final Action nextPred = tool.getNextPred();
            final Location loc = nextPred.getDefinition();
            // We do not support hit count with state-level stepping because stepping back
            // to level/diameter < bp.getHits() does not work.
            return loc.includes(bp.getLocation());
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

        public TLCCapabilities(final boolean reverse) {
            super();
            setSupportsStepBack(reverse);
        }
    }
}
