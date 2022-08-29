// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:40 PST by lamport
//      modified on Sat Jul 28 00:36:09 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tla2sany.semantic.LevelConstants;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.util.Context;

abstract class LNState extends LiveExprNode {
    private final Context con;
    private int tag;

    protected LNState(final Context con) {
        this.con = con;
    }

    @Override
    public final int getLevel() {
        return LevelConstants.VariableLevel;
    }

    @Override
    public final boolean containAction() {
        return false;
    }

    public final boolean eval(final ITool tool, final TLCState s) {
        return this.eval(tool, s, tool.getEmptyState());
    }

    public final Context getContext() {
        return this.con;
    }

    public final int getTag() {
        return this.tag;
    }

    private void setTag(final int t) {
        this.tag = t;
    }

    @Override
    public int tagExpr(final int tag) {
        setTag(tag);
        return tag + 1;
    }

    @Override
    public boolean equals(final LiveExprNode exp) {
        if (exp instanceof LNState lns) {
            return getTag() == lns.getTag();
        }
        return false;
    }
}
