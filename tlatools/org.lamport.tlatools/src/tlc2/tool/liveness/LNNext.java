// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:39 PST by lamport
//      modified on Sat Jul 28 00:36:03 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tla2sany.semantic.LevelConstants;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;

class LNNext extends LiveExprNode {
    private final LiveExprNode body;

    public LNNext(final LiveExprNode body) {
        this.body = body;
    }

    public final LiveExprNode getBody() {
        return this.body;
    }

    @Override
    public final int getLevel() {
        return LevelConstants.ActionLevel;
    }

    @Override
    public final boolean containAction() {
        return this.body.containAction();
    }

    @Override
    public final boolean isPositiveForm() {
        return this.body.isPositiveForm();
    }

    @Override
    public final boolean eval(final ITool tool, final TLCState s1, final TLCState s2) {
        return this.body.eval(tool, s2, tool.getEmptyState());
    }

    @Override
    public final void toString(final StringBuilder sb, final String padding) {
        sb.append("()");
        this.getBody().toString(sb, padding + "  ");
    }

    @Override
    public void extractPromises(final TBPar promises) {
        getBody().extractPromises(promises);
    }

    @Override
    public final LiveExprNode makeBinary() {
        return new LNNext(getBody().makeBinary());
    }

    @Override
    public LiveExprNode flattenSingleJunctions() {
        return new LNNext(getBody().flattenSingleJunctions());
    }

    @Override
    public boolean equals(final LiveExprNode exp) {
        if (exp instanceof LNNext lnn) {
            return getBody().equals(lnn.getBody());
        }
        return false;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.LiveExprNode#toDotViz()
     */
    @Override
    public String toDotViz() {
        return "()" + getBody().toDotViz();
    }
}
