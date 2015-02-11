// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:39 PST by lamport
//      modified on Fri Sep 22 13:56:36 PDT 2000 by yuanyu

package tlc2.tool.liveness;

import tlc2.output.EC;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import util.Assert;

/**
 * Handles evantually (<>)
 *
 * @author Leslie Lamport, Yuan Yu, Simon Zambrovski
 * @version $Id$
 */
class LNEven extends LiveExprNode {
	private static final String EVENTUALLY = "<>";
	protected LiveExprNode body;

	public LNEven(LiveExprNode body) {
		this.body = body;
	}

	public final LiveExprNode getBody() {
		return this.body;
	}

	public final int getLevel() {
		return 3;
	}

	public final boolean containAction() {
		return this.body.containAction();
	}

	public final boolean eval(Tool tool, TLCState s1, TLCState s2) {
		Assert.fail(EC.TLC_LIVE_CANNOT_EVAL_FORMULA, EVENTUALLY);
		return false; // make compiler happy
	}

	public final void toString(StringBuffer sb, String padding) {
		sb.append(EVENTUALLY);
		this.getBody().toString(sb, padding + "  ");
	}
	
	public LiveExprNode getEABody() {
		LiveExprNode evenBody = getBody();
		if (evenBody instanceof LNAll) {
			return ((LNAll) evenBody).getBody();
		}
		return super.getEABody();
	}

	public void extractPromises(TBPar promises) {
		LNEven lne = (LNEven) this;
		if (!promises.member(lne)) {
			promises.addElement(lne);
		}
		lne.getBody().extractPromises(promises);
	}

	public int tagExpr(int tag) {
		return getBody().tagExpr(tag);
	}

	public final LiveExprNode makeBinary() {
		return new LNEven(getBody().makeBinary());
	}

	public LiveExprNode flattenSingleJunctions() {
		return new LNEven(getBody().flattenSingleJunctions());
	}

	public LiveExprNode simplify() {
		LiveExprNode body1 = getBody().simplify();
		if (body1 instanceof LNEven) {
			body1 = ((LNEven) body1).getBody();
		}
		return new LNEven(body1);
	}

	public boolean isGeneralTF() {
		LiveExprNode evenBody = getBody();
		if (evenBody instanceof LNAll) {
			return false;
		}
		return super.isGeneralTF();
	}

	public LiveExprNode pushNeg() {
		return new LNAll(getBody().pushNeg());
	}

	/**
	 * This method pushes a negation all the way down to the atoms. It is
	 * currently not used.
	 */
	public LiveExprNode pushNeg(boolean hasNeg) {
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
	public boolean equals(LiveExprNode exp) {
		if (exp instanceof LNEven) {
			return getBody().equals(((LNEven) exp).getBody());
		}
		return false;
	}
}
