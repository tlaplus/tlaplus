// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:38 PST by lamport
//      modified on Sun Aug  5 00:49:49 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.TLCState;
import tlc2.tool.Tool;

class LNBool extends LiveExprNode {
	public static final LNBool TRUE = new LNBool(true);
	public static final LNBool FALSE = new LNBool(false);

	protected final boolean b;

	public LNBool(boolean b) {
		this.b = b;
	}

	public final boolean eval(Tool tool, TLCState s1, TLCState s2) {
		return this.b;
	}

	public final int getLevel() {
		return 0;
	}

	public final boolean containAction() {
		return false;
	}

	public final void toString(StringBuffer sb, String padding) {
		sb.append(this.b ? "TRUE" : "FALSE");
	}

	public LiveExprNode pushNeg() {
		return new LNBool(!b);
	}

	/**
	 * This method pushes a negation all the way down to the atoms. It is
	 * currently not used.
	 */
	public LiveExprNode pushNeg(boolean hasNeg) {
		// for the remaining types, negate when needed:
		if (hasNeg) {
			return new LNBool(!b);
		}
		return super.pushNeg(hasNeg);
	}

	public boolean equals(LiveExprNode exp) {
		if (exp instanceof LNBool) {
			return b == ((LNBool) exp).b;
		}
		return false;
	}
}
