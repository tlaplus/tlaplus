// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:14 PST by lamport
//      modified on Sun Aug  5 00:13:41 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.output.EC;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import util.Assert;

import java.util.ArrayList;

class LNConj extends LiveExprNode {
    private final ArrayList<LiveExprNode> conjs; // The conjuncts
    private int info;

    public LNConj(final int size) {
        this.conjs = new ArrayList<>(size);
        this.info = 0;
    }

    public LNConj(final LiveExprNode n) {
        this.conjs = new ArrayList<>(1);
        this.conjs.add(n);
        final int level = n.getLevel();
        this.info = n.containAction() ? level + 8 : level;
    }

    public LNConj(final LiveExprNode n1, final LiveExprNode n2) {
        this.conjs = new ArrayList<>(2);
        this.conjs.add(n1);
        this.conjs.add(n2);
        final boolean hasAct = n1.containAction() || n2.containAction();
        final int level = Math.max(n1.getLevel(), n2.getLevel());
        this.info = hasAct ? level + 8 : level;
    }

    public LNConj(final ArrayList<LiveExprNode> conjs) {
        this.conjs = conjs;
        boolean hasAct = false;
        int level = 0;
        for (final LiveExprNode lexpr : conjs) {
            level = Math.max(level, lexpr.getLevel());
            hasAct = hasAct || lexpr.containAction();
        }
        this.info = hasAct ? level + 8 : level;
    }

    public final int getCount() {
        return this.conjs.size();
    }

    public final LiveExprNode getBody(final int i) {
        return this.conjs.get(i);
    }

    public final void addConj(final LiveExprNode elem) {
        if (elem instanceof final LNConj elem1) {
            for (int i = 0; i < elem1.getCount(); i++) {
                this.addConj(elem1.getBody(i));
            }
        } else {
            this.conjs.add(elem);
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
        for (final LiveExprNode lexpr : conjs) {
            if (!lexpr.isPositiveForm()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public final boolean eval(final ITool tool, final TLCState s1, final TLCState s2) {
        final int sz = this.conjs.size();
        for (final LiveExprNode item : this.conjs) {
            if (!item.eval(tool, s1, s2)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public final void toString(final StringBuilder sb, final String padding) {
        final int len = this.getCount();
        final String padding1 = padding + "    ";
        for (int i = 0; i < len; i++) {
            if (i != 0) {
                sb.append(padding);
            }
            sb.append("/\\ (");
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
            sb.append("/\\ (");
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
        final LNConj left = new LNConj(0);
        final LNConj right = new LNConj(0);
        for (int i = 0; i < getCount(); i++) {
            if (i < mid) {
                left.addConj(getBody(i));
            } else {
                right.addConj(getBody(i));
            }
        }
        return new LNConj(left.makeBinary(), right.makeBinary());
    }

    @Override
    public LiveExprNode flattenSingleJunctions() {
        if (getCount() == 1) {
            return getBody(0).flattenSingleJunctions();
        }
        final LNConj lnc2 = new LNConj(getCount());
        for (int i = 0; i < getCount(); i++) {
            lnc2.addConj(getBody(i).flattenSingleJunctions());
        }
        return lnc2;
    }

    /**
     * The method toDNF turns a LiveExprNode into disjunctive normal form.
     */
    @Override
    public final LiveExprNode toDNF() {
        final int count = getCount();
        final LiveExprNode[] temp = new LiveExprNode[count];
        for (int i = 0; i < count; i++) {
            temp[i] = getBody(i).toDNF();
        }

        // We now construct the cross product:
        final ArrayList<LiveExprNode> nes = new ArrayList<>(count);
        int total = 1;
        for (int i = 0; i < count; i++) {
            final LiveExprNode elem = temp[i];
            if (elem instanceof LNDisj lnd) {
                nes.add(elem);
                try {
                    total = Math.multiplyExact(total, ((LNDisj) elem).getCount());
                } catch (ArithmeticException e) {
                    Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA,
                            "because it exceeds the maximum supported size in disjunctive normal form.");
                }
            } else if (elem instanceof final LNConj elem1) {
                // Flatten when elem is also a LNConj:
                final int count1 = elem1.getCount();
                for (int j = 0; j < count1; j++) {
                    nes.add(elem1.getBody(j));
                }
            } else {
                nes.add(elem);
            }
        }

        if (total == 1) {
            return new LNConj(nes);
        }
        final int nesSize = nes.size();
        final ArrayList<LiveExprNode> res = new ArrayList<>(total);
        for (int i = 0; i < total; i++) {
            res.add(new LNConj(nesSize));
        }
        int num = 1;
        int rCount = total;
        for (final LiveExprNode ln : nes) {
            if (ln instanceof final LNDisj disj) {
                rCount = rCount / disj.getCount();
                int idx = 0;
                for (int j = 0; j < num; j++) {
                    for (int k = 0; k < disj.getCount(); k++) {
                        final LiveExprNode elem = disj.getBody(k);
                        for (int l = 0; l < rCount; l++) {
                            ((LNConj) res.get(idx++)).addConj(elem);
                        }
                    }
                }
                num = num * disj.getCount();
            } else {
                for (int j = 0; j < total; j++) {
                    ((LNConj) res.get(j)).addConj(ln);
                }
            }
        }
        return new LNDisj(res);
    }

    @Override
    public LiveExprNode simplify() {
        final LNConj lnc1 = new LNConj(getCount());
        for (int i = 0; i < getCount(); i++) {
            final LiveExprNode elem = getBody(i).simplify();
            if (elem instanceof LNBool lnb) {
                if (!lnb.b) {
                    return LNBool.FALSE;
                }
            } else {
                lnc1.addConj(elem);
            }
        }
        if (lnc1.getCount() == 0) {
            return LNBool.TRUE;
        }
        if (lnc1.getCount() == 1) {
            return lnc1.getBody(0);
        }
        return lnc1;
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
        final LNDisj lnd = new LNDisj(getCount());
        for (int i = 0; i < getCount(); i++) {
            lnd.addDisj(getBody(i).pushNeg());
        }
        return lnd;
    }

    @Override
    public LiveExprNode pushNeg(final boolean hasNeg) {
        if (hasNeg) {
            final LNDisj lnd = new LNDisj(getCount());
            for (int i = 0; i < getCount(); i++) {
                lnd.addDisj(getBody(i).pushNeg(true));
            }
            return lnd;
        } else {
            final LNConj lnc1 = new LNConj(getCount());
            for (int i = 0; i < getCount(); i++) {
                lnc1.addConj(getBody(i).pushNeg(false));
            }
            return lnc1;
        }
    }

    @Override
    public boolean equals(final LiveExprNode exp) {
        if (exp instanceof final LNConj exp2) {
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
