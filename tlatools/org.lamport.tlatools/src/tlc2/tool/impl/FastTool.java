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
import tlc2.tool.IActionItemList;
import tlc2.tool.INextStateFunctor;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.util.ExpectInlined;
import tlc2.value.impl.Value;
import util.FilenameToStream;

import java.util.HashMap;
import java.util.Map;

public final class FastTool extends Tool {

    private static final long serialVersionUID = -2731198442040450257L;

    public FastTool(final String mainFile, final String configFile) {
        super(mainFile, configFile);
    }

    public FastTool(final String mainFile, final String configFile, final FilenameToStream resolver) {
        super(mainFile, configFile, resolver, new HashMap<>());
    }

    public FastTool(final String mainFile, final String configFile, final FilenameToStream resolver, final Map<String, Object> params) {
        super(mainFile, configFile, resolver, params);
    }

    public FastTool(final String mainFile, final String configFile, final FilenameToStream resolver, final Mode mode) {
        super(mainFile, configFile, resolver, mode, new HashMap<>());
    }

    public FastTool(final String mainFile, final String configFile, final FilenameToStream resolver, final Mode mode, final Map<String, Object> params) {
        super(mainFile, configFile, resolver, mode, params);
    }

    public FastTool(final String specDir, final String specFile, final String configFile, final FilenameToStream fts) {
        super(specDir, specFile, configFile, fts, new HashMap<>());
    }

    public FastTool(final String specDir, final String specFile, final String configFile, final FilenameToStream fts, final Map<String, Object> params) {
        super(specDir, specFile, configFile, fts, params);
    }

    public FastTool(final String specDir, final String specFile, final String configFile, final FilenameToStream fts, final Mode mode) {
        super(specDir, specFile, configFile, fts, mode, new HashMap<>());
    }

    public FastTool(final Tool tool) {
        super(tool);
    }

    // The methods below are supposed to be inlined during execution for performance
    // reasons, collapsing this class effectively into Tool. Later and in case of a
    // violation, the FastTool instance will be exchanged for the CallStackTool
    // instance that properly records error for the purpose of error reporting.
    @ExpectInlined
    @Override
    protected TLCState getNextStates(final Action action, final SemanticNode pred, final ActionItemList acts,
                                     final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
        return getNextStatesImpl(action, pred, acts, c, s0, s1, nss, cm);
    }

    @ExpectInlined
    @Override
    protected TLCState getNextStatesAppl(final Action action, final OpApplNode pred, final ActionItemList acts,
                                         final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
        return getNextStatesApplImpl(action, pred, acts, c, s0, s1, nss, cm);
    }

    @ExpectInlined
    @Override
    protected TLCState processUnchanged(final Action action, final SemanticNode expr, final ActionItemList acts,
                                        final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
        return processUnchangedImpl(action, expr, acts, c, s0, s1, nss, cm);
    }

    @ExpectInlined
    @Override
    public Value eval(final SemanticNode expr, final Context c, final TLCState s0, final TLCState s1,
                      final int control, final CostModel cm) {
        return evalImpl(expr, c, s0, s1, control, cm);
    }

    @ExpectInlined
    @Override
    protected Value evalAppl(final OpApplNode expr, final Context c, final TLCState s0, final TLCState s1,
                             final int control, final CostModel cm) {
        return evalApplImpl(expr, c, s0, s1, control, cm);
    }

    @ExpectInlined
    @Override
    protected Value setSource(final SemanticNode expr, final Value value) {
        return value;
    }

    @ExpectInlined
    @Override
    public TLCState enabled(final SemanticNode pred, final IActionItemList acts, final Context c,
                            final TLCState s0, final TLCState s1, final CostModel cm) {
        return enabledImpl(pred, (ActionItemList) acts, c, s0, s1, cm); // TODO This cast sucks performance-wise.
    }

    @ExpectInlined
    @Override
    protected TLCState enabledAppl(final OpApplNode pred, final ActionItemList acts, final Context c,
                                   final TLCState s0, final TLCState s1, final CostModel cm) {
        return enabledApplImpl(pred, acts, c, s0, s1, cm);
    }

    @ExpectInlined
    @Override
    protected TLCState enabledUnchanged(final SemanticNode expr, final ActionItemList acts, final Context c,
                                        final TLCState s0, final TLCState s1, final CostModel cm) {
        return enabledUnchangedImpl(expr, acts, c, s0, s1, cm);
    }
}
