// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:40 PST by lamport
//      modified on Sat Jul 28 00:36:09 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.util.Context;

abstract class LNState extends LiveExprNode {
	private final Context con;
	private int tag;

	public LNState(Context con) {
		this.con = con;
	}

	public final int getLevel() {
		return 1;
	}

	public final boolean containAction() {
		return false;
	}

	public final boolean eval(ITool tool, TLCState s) {
		return this.eval(tool, s, TLCState.Empty);
	}

	public final Context getContext() {
		return this.con;
	}

	public final int getTag() {
		return this.tag;
	}

	public final void setTag(int t) {
		this.tag = t;
	}

	public int tagExpr(int tag) {
		setTag(tag);
		return tag + 1;
	}

	public boolean equals(LiveExprNode exp) {
		if (exp instanceof LNState) {
			return getTag() == ((LNState) exp).getTag();
		}
		return false;
	}
}
