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
 *   William Schultz - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TraceAnimationView;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A data provider for runs of the trace animator.
 * 
 * This inherits most of its core functionality from the
 * TraceExplorerDataProvider. It receives output from the appropriate
 * TraceExplorerJob and processes it for display in the animation viewer. Note
 * that trace exploration and trace animation share nearly all of the same
 * functionality. They differ, however, in how they choose to present the data
 * from the explored trace.
 * 
 * @author William Schultz
 */
public class TraceAnimatorDataProvider extends TraceExplorerDataProvider {

    /**
     * Override this method to return the file used for trace animation.
     */
    @Override
    protected IFile getTraceFile() {
        return getModel().getTraceAnimatorTLAFile();
    }

    public TraceAnimatorDataProvider(Model model) {
        super(model);
    }

    /**
     * Connect to the source registry for trace animation.
     */
    protected void connectToSourceRegistry() {
        TLCOutputSourceRegistry.getTraceAnimateSourceRegistry().connect(this);
    }

    /**
     * Extracts each SVG frame of the animated trace and displays them in the trace
     * animation viewer.
     */
    @Override
    protected void postProcess() {
        UIHelper.runUIAsync(new Runnable() {

            public void run() {
                // Extract the animated trace and open the viewer.
                TraceAnimationView view = (TraceAnimationView) UIHelper.openView(TraceAnimationView.ID);
                ArrayList<String> svgFrames = constructTraceAnimation();
                view.setSVGAnimationFrames(svgFrames);
                view.loadInitialFrame();
                view.setFocus();
            }
        });
    }

    /**
     * Processes the trace from the TLC run and extracts the evaluated 'View'
     * expression from each state and compiles it into a sequence of SVG frames.
     */
    public ArrayList<String> constructTraceAnimation() {
        ArrayList<String> svgStates = new ArrayList<String>();
        for (TLCError e : getErrors()) {
            for (TLCState s : e.getStates()) {
                for (TLCVariable v : s.getVariablesAsList()) {
                    if (v.getName().equals("View")) {
                        svgStates.add(v.getValue().toString());
                    }
                }
            }
        }
        return svgStates;
    }

}
