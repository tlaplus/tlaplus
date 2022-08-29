// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:37 PST by lamport
//      modified on Fri Sep 22 13:54:35 PDT 2000 by yuanyu

package tlc2.tool.liveness;

import tla2sany.semantic.LevelConstants;
import tlc2.output.EC;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import util.Assert;

/**
 * Handles always ([])
 *
 * @author Leslie Lamport, Yuan Yu, Simon Zambrovski
 * @version $Id$
 */
class LNAll extends LiveExprNode {
    /**
     *
     */
    private static final String ALWAYS = "[]";
    private final LiveExprNode body;

    public LNAll(final LiveExprNode body) {
        this.body = body;
    }

    public final LiveExprNode getBody() {
        return this.body;
    }

    @Override
    public final int getLevel() {
        return LevelConstants.TemporalLevel;
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
        Assert.fail(EC.TLC_LIVE_CANNOT_EVAL_FORMULA, ALWAYS);
        return false; // make compiler happy
    }

    @Override
    public final void toString(final StringBuilder sb, final String padding) {
        sb.append(ALWAYS);
        this.getBody().toString(sb, padding + "  ");
    }

    /* Return A if this expression is of form []<>A. */
    @Override
    public LiveExprNode getAEBody() {
        final LiveExprNode allBody = getBody();
        if (allBody instanceof LNEven lne) {
            return lne.getBody();
        }
        return super.getAEBody();
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
        return new LNAll(getBody().makeBinary());
    }

    @Override
    public LiveExprNode flattenSingleJunctions() {
        return new LNAll(getBody().flattenSingleJunctions());
    }

    @Override
    public LiveExprNode simplify() {
        LiveExprNode body1 = getBody().simplify();
        if (body1 instanceof LNAll lna) {
            body1 = lna.getBody();
        }
        return new LNAll(body1);
    }

    @Override
    public boolean isGeneralTF() {
        final LiveExprNode allBody = getBody();
        if (allBody instanceof LNEven) {
            return false;
        }
        return super.isGeneralTF();
    }

    @Override
    public LiveExprNode pushNeg() {
        return new LNEven(getBody().pushNeg());
    }

    @Override
    public LiveExprNode pushNeg(final boolean hasNeg) {
        if (hasNeg) {
            return new LNEven(getBody().pushNeg(true));
        } else {
            return new LNAll(getBody().pushNeg(false));
        }
    }

    @Override
    public boolean equals(final LiveExprNode exp) {
        if (exp instanceof LNAll lna) {
            return getBody().equals(lna.getBody());
        }
        return false;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.LiveExprNode#toDotViz()
     */
    @Override
    public String toDotViz() {
        return ALWAYS + getBody().toDotViz();
    }
}
