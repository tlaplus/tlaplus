// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:39 PST by lamport
//      modified on Sat Jul 28 00:35:57 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.TLCState;
import tlc2.tool.Tool;

public class LNNeg extends LiveExprNode {
	private LiveExprNode body;

	public LNNeg(LiveExprNode body) {
		this.body = body;
	}

	public final LiveExprNode getBody() {
		return this.body;
	}

	public final int getLevel() {
		return this.body.getLevel();
	}

	public final boolean containAction() {
		return this.body.containAction();
	}

	public final boolean eval(Tool tool, TLCState s1, TLCState s2) {
		return !this.body.eval(tool, s1, s2);
	}

	public final void toString(StringBuffer sb, String padding) {
		sb.append("-");
		this.getBody().toString(sb, padding + " ");
	}

	public void extractPromises(TBPar promises) {
		getBody().extractPromises(promises);
	}

	public int tagExpr(int tag) {
		return getBody().tagExpr(tag);
	}

	public final LiveExprNode makeBinary() {
		return new LNNeg(getBody().makeBinary());
	}

	public LiveExprNode flattenSingleJunctions() {
		LiveExprNode ln1 = getBody();
		if (ln1 instanceof LNNeg) {
			return ((LNNeg) ln1).getBody().flattenSingleJunctions();
		}
		return new LNNeg(ln1.flattenSingleJunctions());
	}

	public final LiveExprNode toDNF() {
		LiveExprNode body = getBody();
		if ((body instanceof LNState) || (body instanceof LNAction)) {
			return this;
		}
		return body.pushNeg().toDNF();
	}

	public LiveExprNode simplify() {
		LiveExprNode body1 = getBody().simplify();
		if (body1 instanceof LNBool) {
			return new LNBool(!((LNBool) body1).b);
		}
		return new LNNeg(body1);
	}

	public boolean isGeneralTF() {
		return getBody().isGeneralTF();
	}

	public LiveExprNode pushNeg() {
		return getBody();
	}

	public LiveExprNode pushNeg(boolean hasNeg) {
		LiveExprNode lexpr = getBody();
		return lexpr.pushNeg(!hasNeg);
	}

	/**
	 * This method returns true or false for whether two LiveExprNodes are
	 * syntactically equal.
	 */
	public boolean equals(LiveExprNode exp) {
		if (exp instanceof LNNeg) {
			return getBody().equals(((LNNeg) exp).getBody());
		}
		return false;
	}
}
