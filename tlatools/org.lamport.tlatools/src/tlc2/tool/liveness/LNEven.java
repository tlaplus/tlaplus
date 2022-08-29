// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:39 PST by lamport
//      modified on Fri Sep 22 13:56:36 PDT 2000 by yuanyu

package tlc2.tool.liveness;

import tla2sany.semantic.LevelConstants;
import tlc2.output.EC;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import util.Assert;

/**
 * Handles evantually (<>)
 *
 * @author Leslie Lamport, Yuan Yu, Simon Zambrovski
 * @version $Id$
 */
class LNEven extends LiveExprNode {
    private static final String EVENTUALLY = "<>";
    private final LiveExprNode body;

    public LNEven(final LiveExprNode body) {
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
        Assert.fail(EC.TLC_LIVE_CANNOT_EVAL_FORMULA, EVENTUALLY);
        return false; // make compiler happy
    }

    @Override
    public final void toString(final StringBuilder sb, final String padding) {
        sb.append(EVENTUALLY);
        this.getBody().toString(sb, padding + "  ");
    }

    @Override
    public LiveExprNode getEABody() {
        final LiveExprNode evenBody = getBody();
        if (evenBody instanceof LNAll lna) {
            return lna.getBody();
        }
        return super.getEABody();
    }

    @Override
    public void extractPromises(final TBPar promises) {
        final LNEven lne = this;
        if (!promises.member(lne)) {
            promises.add(lne);
        }
        lne.getBody().extractPromises(promises);
    }

    @Override
    public int tagExpr(final int tag) {
        return getBody().tagExpr(tag);
    }

    @Override
    public final LiveExprNode makeBinary() {
        return new LNEven(getBody().makeBinary());
    }

    @Override
    public LiveExprNode flattenSingleJunctions() {
        return new LNEven(getBody().flattenSingleJunctions());
    }

    @Override
    public LiveExprNode simplify() {
        LiveExprNode body1 = getBody().simplify();
        if (body1 instanceof LNEven lne) {
            body1 = lne.getBody();
        }
        return new LNEven(body1);
    }

    @Override
    public boolean isGeneralTF() {
        final LiveExprNode evenBody = getBody();
        if (evenBody instanceof LNAll) {
            return false;
        }
        return super.isGeneralTF();
    }

    @Override
    public LiveExprNode pushNeg() {
        return new LNAll(getBody().pushNeg());
    }

    /**
     * This method pushes a negation all the way down to the atoms. It is
     * currently not used.
     */
    @Override
    public LiveExprNode pushNeg(final boolean hasNeg) {
        if (hasNeg) {
            return new LNAll(getBody().pushNeg(true));
        } else {
            return new LNEven(getBody().pushNeg(false));
        }
    }

    /**
     * This method returns true or false for whether two LiveExprNodes are
     * syntactically equal.
     */
    @Override
    public boolean equals(final LiveExprNode exp) {
        if (exp instanceof LNEven lne) {
            return getBody().equals(lne.getBody());
        }
        return false;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.LiveExprNode#toDotViz()
     */
    @Override
    public String toDotViz() {
        return EVENTUALLY + getBody().toDotViz();
    }
}
