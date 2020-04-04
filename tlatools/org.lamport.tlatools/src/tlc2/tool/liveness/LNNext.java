// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:39 PST by lamport
//      modified on Sat Jul 28 00:36:03 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.ITool;
import tlc2.tool.TLCState;

class LNNext extends LiveExprNode {
	private final LiveExprNode body;

	public LNNext(LiveExprNode body) {
		this.body = body;
	}

	public final LiveExprNode getBody() {
		return this.body;
	}

	public final int getLevel() {
		return 2;
	}

	public final boolean containAction() {
		return this.body.containAction();
	}

	public final boolean eval(ITool tool, TLCState s1, TLCState s2) {
		return this.body.eval(tool, s2, TLCState.Empty);
	}

	public final void toString(StringBuffer sb, String padding) {
		sb.append("()");
		this.getBody().toString(sb, padding + "  ");
	}

	public void extractPromises(TBPar promises) {
		getBody().extractPromises(promises);
	}

	public final LiveExprNode makeBinary() {
		return new LNNext(getBody().makeBinary());
	}

	public LiveExprNode flattenSingleJunctions() {
		return new LNNext(getBody().flattenSingleJunctions());
	}

	public boolean equals(LiveExprNode exp) {
		if (exp instanceof LNNext) {
			return getBody().equals(((LNNext) exp).getBody());
		}
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.LiveExprNode#toDotViz()
	 */
	public String toDotViz() {
		return "()" + getBody().toDotViz();
	}
}
