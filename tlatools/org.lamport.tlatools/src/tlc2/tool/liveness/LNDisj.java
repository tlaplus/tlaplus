// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:38 PST by lamport
//      modified on Sun Aug  5 00:14:58 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.ITool;
import tlc2.tool.TLCState;

import java.util.ArrayList;

class LNDisj extends LiveExprNode {
    private final ArrayList<LiveExprNode> disjs; // The disjuncts
    private int info;

    public LNDisj(final int size) {
        this.disjs = new ArrayList<>(size);
        this.info = 0;
    }

    public LNDisj(final LiveExprNode n) {
        this.disjs = new ArrayList<>(1);
        this.disjs.add(n);
        final int level = n.getLevel();
        this.info = n.containAction() ? level + 8 : level;
    }

    public LNDisj(final LiveExprNode n1, final LiveExprNode n2) {
        this.disjs = new ArrayList<>(2);
        this.disjs.add(n1);
        this.disjs.add(n2);
        final boolean hasAct = n1.containAction() || n2.containAction();
        final int level = Math.max(n1.getLevel(), n2.getLevel());
        this.info = hasAct ? level + 8 : level;
    }

    public LNDisj(final ArrayList<LiveExprNode> disjs) {
        this.disjs = disjs;
        boolean hasAct = false;
        int level = 0;
        for (final LiveExprNode lexpr : disjs) {
            level = Math.max(level, lexpr.getLevel());
            hasAct = hasAct || lexpr.containAction();
        }
        this.info = hasAct ? level + 8 : level;
    }

    public final int getCount() {
        return this.disjs.size();
    }

    public final LiveExprNode getBody(final int i) {
        return this.disjs.get(i);
    }

    public final void addDisj(final LiveExprNode elem) {
        if (elem instanceof final LNDisj elem1) {
            for (int i = 0; i < elem1.getCount(); i++) {
                this.addDisj(elem1.getBody(i));
            }
        } else {
            this.disjs.add(elem);
        }
        final int level = Math.max(this.getLevel(), elem.getLevel());
        final boolean hasAct = this.containAction() || elem.containAction();
        this.info = hasAct ? level + 8 : level;
    }

    @Override
    public final int getLevel() {
        return (this.info & 7);
    }

    @Override
    public final boolean containAction() {
        return (this.info & 8) > 0;
    }

    @Override
    public final boolean isPositiveForm() {
        for (final LiveExprNode lexpr : disjs) {
            if (!lexpr.isPositiveForm()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public final boolean eval(final ITool tool, final TLCState s1, final TLCState s2) {
        final int sz = disjs.size();
        for (final LiveExprNode item : disjs) {
            if (item.eval(tool, s1, s2)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public final void toString(final StringBuilder sb, final String padding) {
        final int len = this.getCount();
        final String padding1 = padding + "    ";
        for (int i = 0; i < len; i++) {
            if (i != 0) {
                sb.append(padding);
            }
            sb.append("\\/ (");
            this.getBody(i).toString(sb, padding1);
            sb.append(")");
            if (i != len - 1) {
                sb.append("\n");
            }
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.LiveExprNode#toDotViz()
     */
    @Override
    public String toDotViz() {
        final int len = this.getCount();
        final StringBuilder sb = new StringBuilder(len);
        for (int i = 0; i < len; i++) {
            sb.append("\\/ (");
            sb.append(this.getBody(i).toDotViz());
            sb.append(")");
            if (i != len - 1) {
                sb.append("\n");
            }
        }
        return sb.toString();
    }

    @Override
    public void extractPromises(final TBPar promises) {
        getBody(0).extractPromises(promises);
        getBody(1).extractPromises(promises);
    }

    @Override
    public int tagExpr(int tag) {
        for (int i = 0; i < getCount(); i++) {
            tag = getBody(i).tagExpr(tag);
        }
        return tag;
    }

    @Override
    public final LiveExprNode makeBinary() {
        if (getCount() == 1) {
            return getBody(0).makeBinary();
        }
        final int mid = getCount() / 2;
        final LNDisj left = new LNDisj(0);
        final LNDisj right = new LNDisj(0);
        for (int i = 0; i < getCount(); i++) {
            if (i < mid) {
                left.addDisj(getBody(i));
            } else {
                right.addDisj(getBody(i));
            }
        }
        return new LNDisj(left.makeBinary(), right.makeBinary());
    }

    @Override
    public LiveExprNode flattenSingleJunctions() {
        if (getCount() == 1) {
            return getBody(0).flattenSingleJunctions();
        }
        final LNDisj lnd2 = new LNDisj(getCount());
        for (int i = 0; i < getCount(); i++) {
            lnd2.addDisj(getBody(i).flattenSingleJunctions());
        }
        return lnd2;
    }

    // Apply []<>A1 \/ []<>A2 = []<>(A1 \/ A2) when possible.
    @Override
    public final LiveExprNode toDNF() {
        final LNDisj aeRes = new LNDisj(0);
        final LNDisj res = new LNDisj(0);
        for (int i = 0; i < getCount(); i++) {
            final LiveExprNode elem = getBody(i).toDNF();
            if (elem instanceof final LNDisj disj1) {
                for (int j = 0; j < disj1.getCount(); j++) {
                    final LiveExprNode elem1 = disj1.getBody(j);
                    final LiveExprNode elemBody = elem1.getAEBody();
                    if (elemBody == null) {
                        res.addDisj(elem1);
                    } else {
                        aeRes.addDisj(elemBody);
                    }
                }
            } else {
                final LiveExprNode elemBody = elem.getAEBody();
                if (elemBody == null) {
                    res.addDisj(elem);
                } else {
                    aeRes.addDisj(elemBody);
                }
            }
        }
        // Add aeRes to res before returning.
        if (aeRes.getCount() == 1) {
            res.addDisj(new LNAll(new LNEven(aeRes.getBody(0))));
        } else if (aeRes.getCount() > 1) {
            res.addDisj(new LNAll(new LNEven(aeRes)));
        }
        return res;
    }

    @Override
    public LiveExprNode simplify() {
        final LNDisj lnd1 = new LNDisj(getCount());
        for (int i = 0; i < getCount(); i++) {
            final LiveExprNode elem = getBody(i).simplify();
            if (elem instanceof LNBool lnb) {
                if (lnb.b) {
                    return LNBool.TRUE;
                }
            } else {
                lnd1.addDisj(elem);
            }
        }
        if (lnd1.getCount() == 0) {
            return LNBool.FALSE;
        }
        if (lnd1.getCount() == 1) {
            return lnd1.getBody(0);
        }
        return lnd1;
    }

    @Override
    public boolean isGeneralTF() {
        for (int i = 0; i < getCount(); i++) {
            if (!getBody(i).isGeneralTF()) {
                return false;
            }
        }
        return super.isGeneralTF();
    }

    @Override
    public LiveExprNode pushNeg() {
        final LNConj lnc = new LNConj(getCount());
        for (int i = 0; i < getCount(); i++) {
            lnc.addConj(getBody(i).pushNeg());
        }
        return lnc;
    }

    @Override
    public LiveExprNode pushNeg(final boolean hasNeg) {
        if (hasNeg) {
            final LNConj lnc = new LNConj(getCount());
            for (int i = 0; i < getCount(); i++) {
                lnc.addConj(getBody(i).pushNeg(true));
            }
            return lnc;
        } else {
            final LNDisj lnd1 = new LNDisj(getCount());
            for (int i = 0; i < getCount(); i++) {
                lnd1.addDisj(getBody(i).pushNeg(false));
            }
            return lnd1;
        }
    }

    /**
     * This method returns true or false for whether two LiveExprNodes are
     * syntactically equal.
     */
    @Override
    public boolean equals(final LiveExprNode exp) {
        if (exp instanceof final LNDisj exp2) {
            if (getCount() != exp2.getCount()) {
                return false;
            }
            for (int i = 0; i < getCount(); i++) {
                if (!getBody(i).equals(exp2.getBody(i))) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }
}
