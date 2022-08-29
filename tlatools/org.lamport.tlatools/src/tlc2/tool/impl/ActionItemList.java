// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.tool.impl;

import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.tool.Action;
import tlc2.tool.IActionItemList;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;

class ActionItemList implements IActionItemList {
    public static final ActionItemList
            Empty = new ActionItemList(null, null, 0, null, null);
    protected static final boolean coverage = TLCGlobals.isCoverageEnabled();
    /**
     * We assume that this.pred is null iff the list is empty.
     */
    public final SemanticNode pred;     // Expression of the action
    public final Context con;           // Context of the action
    public final ActionItemList next;
    public final CostModel cm;
    private final int kind;

    /* Constructors */
    protected ActionItemList(final SemanticNode pred, final Context con,
                             final int kind, final ActionItemList next, final CostModel cm) {
        this.pred = pred;
        this.con = con;
        this.kind = kind;
        this.next = next;
        this.cm = cm;
    }

    public final SemanticNode carPred() {
        return this.pred;
    }

    public final Context carContext() {
        return this.con;
    }

    /**
     * The meaning of this.kind is given as follows:
     * kind > 0:  pred of a conjunction
     * kind = -1: pred
     * kind = -2: UNCHANGED pred
     * kind = -3: pred' # pred
     */
    public final int carKind() {
        return this.kind;
    }

    public ActionItemList cdr() {
        return this.next;
    }

    @Override
    public IActionItemList cons(final SemanticNode pred,
                                final Context con, final CostModel cm, final int kind) {
        return new ActionItemList(pred, con, kind, this, coverage ? cm.get(pred) : cm);
    }

    public ActionItemList cons(final Action act, final int kind) {
        return new ActionItemList(act.pred, act.con, kind, this, coverage ? act.cm.get(pred) : act.cm);
    }

    public boolean isEmpty() {
        return (this.pred == null && this.con == null && this.kind == 0 && this.next == null && this.cm == null);
    }

    public ActionItemList getEmpty() {
        return new ActionItemList(null, null, 0, null, null);
    }

    public Action getAction() {
        // no-op here, but overridden by subclass.
        return null;
    }

    public void setAction(final Action action) {
        // no-op here, but overridden by subclass.
    }
}
