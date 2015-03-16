// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:38 PST by lamport
//      modified on Sun Aug  5 00:14:58 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.Vect;

class LNDisj extends LiveExprNode {
	private final Vect disjs; // The disjuncts
	private int info;

	public LNDisj(int size) {
		this.disjs = new Vect(size);
		this.info = 0;
	}

	public LNDisj(LiveExprNode n) {
		this.disjs = new Vect(1);
		this.disjs.addElement(n);
		int level = n.getLevel();
		this.info = n.containAction() ? level + 8 : level;
	}

	public LNDisj(LiveExprNode n1, LiveExprNode n2) {
		this.disjs = new Vect(2);
		this.disjs.addElement(n1);
		this.disjs.addElement(n2);
		boolean hasAct = n1.containAction() || n2.containAction();
		int level = Math.max(n1.getLevel(), n2.getLevel());
		this.info = hasAct ? level + 8 : level;
	}

	public LNDisj(Vect disjs) {
		this.disjs = disjs;
		boolean hasAct = false;
		int level = 0;
		for (int i = 0; i < disjs.size(); i++) {
			LiveExprNode lexpr = (LiveExprNode) disjs.elementAt(i);
			level = Math.max(level, lexpr.getLevel());
			hasAct = hasAct || lexpr.containAction();
		}
		this.info = hasAct ? level + 8 : level;
	}

	public final int getCount() {
		return this.disjs.size();
	}

	public final LiveExprNode getBody(int i) {
		return (LiveExprNode) this.disjs.elementAt(i);
	}

	public final void addDisj(LiveExprNode elem) {
		if (elem instanceof LNDisj) {
			LNDisj elem1 = (LNDisj) elem;
			for (int i = 0; i < elem1.getCount(); i++) {
				this.addDisj(elem1.getBody(i));
			}
		} else {
			this.disjs.addElement(elem);
		}
		int level = Math.max(this.getLevel(), elem.getLevel());
		boolean hasAct = this.containAction() || elem.containAction();
		this.info = hasAct ? level + 8 : level;
	}

	public final int getLevel() {
		return (this.info & 7);
	}

	public final boolean containAction() {
		return (this.info & 8) > 0;
	}

	public final boolean eval(Tool tool, TLCState s1, TLCState s2) {
		int sz = disjs.size();
		for (int i = 0; i < sz; i++) {
			LiveExprNode item = (LiveExprNode) disjs.elementAt(i);
			if (item.eval(tool, s1, s2)) {
				return true;
			}
		}
		return false;
	}

	public final void toString(StringBuffer sb, String padding) {
		int len = this.getCount();
		String padding1 = padding + "    ";
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

	public void extractPromises(TBPar promises) {
		getBody(0).extractPromises(promises);
		getBody(1).extractPromises(promises);
	}

	public int tagExpr(int tag) {
		for (int i = 0; i < getCount(); i++) {
			tag = getBody(i).tagExpr(tag);
		}
		return tag;
	}

	public final LiveExprNode makeBinary() {
		if (getCount() == 1) {
			return getBody(0).makeBinary();
		}
		int mid = getCount() / 2;
		LNDisj left = new LNDisj(0);
		LNDisj right = new LNDisj(0);
		for (int i = 0; i < getCount(); i++) {
			if (i < mid) {
				left.addDisj(getBody(i));
			} else {
				right.addDisj(getBody(i));
			}
		}
		return new LNDisj(left.makeBinary(), right.makeBinary());
	}

	public LiveExprNode flattenSingleJunctions() {
		if (getCount() == 1) {
			return getBody(0).flattenSingleJunctions();
		}
		LNDisj lnd2 = new LNDisj(getCount());
		for (int i = 0; i < getCount(); i++) {
			lnd2.addDisj(getBody(i).flattenSingleJunctions());
		}
		return lnd2;
	}

	// Apply []<>A1 \/ []<>A2 = []<>(A1 \/ A2) when possible.
	public final LiveExprNode toDNF() {
		LNDisj aeRes = new LNDisj(0);
		LNDisj res = new LNDisj(0);
		for (int i = 0; i < getCount(); i++) {
			LiveExprNode elem = getBody(i).toDNF();
			if (elem instanceof LNDisj) {
				LNDisj disj1 = (LNDisj) elem;
				for (int j = 0; j < disj1.getCount(); j++) {
					LiveExprNode elem1 = disj1.getBody(j);
					LiveExprNode elemBody = elem1.getAEBody();
					if (elemBody == null) {
						res.addDisj(elem1);
					} else {
						aeRes.addDisj(elemBody);
					}
				}
			} else {
				LiveExprNode elemBody = elem.getAEBody();
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

	public LiveExprNode simplify() {
		LNDisj lnd1 = new LNDisj(getCount());
		for (int i = 0; i < getCount(); i++) {
			LiveExprNode elem = getBody(i).simplify();
			if (elem instanceof LNBool) {
				if (((LNBool) elem).b) {
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

	public boolean isGeneralTF() {
		for (int i = 0; i < getCount(); i++) {
			if (!getBody(i).isGeneralTF()) {
				return false;
			}
		}
		return super.isGeneralTF();
	}

	public LiveExprNode pushNeg() {
		LNConj lnc = new LNConj(getCount());
		for (int i = 0; i < getCount(); i++) {
			lnc.addConj(getBody(i).pushNeg());
		}
		return lnc;
	}

	public LiveExprNode pushNeg(boolean hasNeg) {
		if (hasNeg) {
			LNConj lnc = new LNConj(getCount());
			for (int i = 0; i < getCount(); i++) {
				lnc.addConj(getBody(i).pushNeg(true));
			}
			return lnc;
		} else {
			LNDisj lnd1 = new LNDisj(getCount());
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
	public boolean equals(LiveExprNode exp) {
		if (exp instanceof LNDisj) {
			LNDisj exp2 = (LNDisj) exp;
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
