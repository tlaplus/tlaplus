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
package org.lamport.tla.toolbox.tool.tlc.launch;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Methods in this class are executed when the user clicks the 'Animate' button
 * on the trace explorer interface. It is an extension of TraceExplorerDelegate
 * due to the fact that trace exploration and trace animation share most of the
 * same logic. Trace animation runs a trace exploration job but only evaluates
 * only the 'view' expression instead of user defined TLA+ expressions.
 */
public class TraceAnimatorDelegate extends TraceExplorerDelegate {
    public static final String MODE_TRACE_ANIMATE = "animateTrace";

    // The name of the 'view' expression to be used for trace animation.
    // For now, this is hard-coded and not externally customizable.
    private static final String viewExpression = "View";

    /**
     * Provide overrides that point to the files to use for trace animation.
     */
    @Override
    protected String getTlaFileName() {
        return ModelHelper.TA_FILE_TLA;
    }

    @Override
    protected String getCfgFileName() {
        return ModelHelper.TA_FILE_CFG;
    }

    @Override
    protected String getOutFileName() {
        return ModelHelper.TA_FILE_OUT;
    }

    @Override
    protected String getModelName() {
        return ModelHelper.TA_MODEL_NAME;
    }

    @Override
    protected IFile getRootModule(Model model) {
        return model.getTAFile();
    }

    protected String getMode() {
        return MODE_TRACE_ANIMATE;
    }

    /**
     * For trace animation, the view expression is the only thing we evaluate.
     */
    @Override
    protected List<Formula> getFormulaList(ILaunchConfiguration config) throws CoreException {
        ArrayList<Formula> viewExpr = new ArrayList<>();
        viewExpr.add(new Formula(viewExpression));
        return viewExpr;
    }
}
