// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:39 PST by lamport
//      modified on Sat Jul 28 00:35:57 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.ITool;
import tlc2.tool.TLCState;

public class LNNeg extends LiveExprNode {
    private final LiveExprNode body;

    public LNNeg(final LiveExprNode body) {
        this.body = body;
    }

    public final LiveExprNode getBody() {
        return this.body;
    }

    @Override
    public final int getLevel() {
        return this.body.getLevel();
    }

    @Override
    public final boolean containAction() {
        return this.body.containAction();
    }

    @Override
    public final boolean isPositiveForm() {
        return this.body instanceof LNBool || this.body instanceof LNState;
    }

    @Override
    public final boolean eval(final ITool tool, final TLCState s1, final TLCState s2) {
        return !this.body.eval(tool, s1, s2);
    }

    @Override
    public final void toString(final StringBuilder sb, final String padding) {
        sb.append("-");
        this.getBody().toString(sb, padding + " ");
    }

    @Override
    public void extractPromises(final TBPar promises) {
        getBody().extractPromises(promises);
    }

    @Override
    public int tagExpr(final int tag) {
        return getBody().tagExpr(tag);
    }

    @Override
    public final LiveExprNode makeBinary() {
        return new LNNeg(getBody().makeBinary());
    }

    @Override
    public LiveExprNode flattenSingleJunctions() {
        final LiveExprNode ln1 = getBody();
        if (ln1 instanceof LNNeg lnn) {
            return lnn.getBody().flattenSingleJunctions();
        }
        return new LNNeg(ln1.flattenSingleJunctions());
    }

    @Override
    public final LiveExprNode toDNF() {
        final LiveExprNode body = getBody();
        if ((body instanceof LNState) || (body instanceof LNAction)) {
            return this;
        }
        return body.pushNeg().toDNF();
    }

    @Override
    public LiveExprNode simplify() {
        final LiveExprNode body1 = getBody().simplify();
        if (body1 instanceof LNBool lnb) {
            return new LNBool(!lnb.b);
        }
        return new LNNeg(body1);
    }

    @Override
    public boolean isGeneralTF() {
        return getBody().isGeneralTF();
    }

    @Override
    public LiveExprNode pushNeg() {
        return getBody();
    }

    @Override
    public LiveExprNode pushNeg(final boolean hasNeg) {
        final LiveExprNode lexpr = getBody();
        return lexpr.pushNeg(!hasNeg);
    }

    /**
     * This method returns true or false for whether two LiveExprNodes are
     * syntactically equal.
     */
    @Override
    public boolean equals(final LiveExprNode exp) {
        if (exp instanceof LNNeg lnn) {
            return getBody().equals(lnn.getBody());
        }
        return false;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.LiveExprNode#toDotViz()
     */
    @Override
    public String toDotViz() {
        return "-" + getBody().toDotViz();
    }
}
