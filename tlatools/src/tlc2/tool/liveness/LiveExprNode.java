// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:18 PST by lamport
//      modified on Sun Aug  5 00:00:56 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.TLCState;
import tlc2.tool.Tool;

/**
 * LNConj - a conjunction. (contains list of conjuncts) LNDisj - a disjunction.
 * (contains list of disjuncts) LNAll - Allways: []e LNEven - Eventually: <>e
 * LNNeg - Negation: -e LNState - State predicate. Concrete types: LNStateAST,
 * LNStateEnabled LNAction - Transition predicate. LNNext - next. ()e. Only used
 * for tableau construction. Not part of TLA
 *
 * LNState and LNAction have tags. When constructing the tableau, we will have
 * to check whether two primitives are equal to each other, to distinguish
 * atoms. We could do it just by checking the object pointers to the Act and
 * State ASTNodes. But to make it absolutely explicit, I will use integer tags.
 * These are initialized to distinct values immediately before tableau
 * construction, used during tableau construction, and not used any more.
 *
 * There's a little bit of a hierarchy for the LNState. That's because
 * LNStateAST (which has just an ASTNode for the state predicate) must be
 * evaluated differently from LNStateEnabled (which has ENABLED ast in it)
 *
 * We are going to end up evaluating LNState and LNAction when we come to
 * construct the tableau graph. That's for the EAs, the EAs, and for local
 * consistency. Therefore LNState and LNAction have appropriate eval functions.
 **/

public abstract class LiveExprNode {
	/**
	 * getLevel() = 0 --> constant getLevel() = 1 --> state expression
	 * getLevel() = 2 --> action expression getLevel() = 3 --> temporal
	 * expression
	 */
	public abstract int getLevel();

	/* Returns true iff the expression contains action. */
	public abstract boolean containAction();

	public abstract boolean eval(Tool tool, TLCState s1, TLCState s2);

	/* The string representation. */
	public final String toString() {
		StringBuffer sb = new StringBuffer();
		this.toString(sb, "");
		return sb.toString();
	}

	public abstract void toString(StringBuffer sb, String padding);

	/**
	 * This method returns true or false for whether two LiveExprNodes are
	 * syntactically equal.
	 */
	public abstract boolean equals(LiveExprNode exp);

	/* Return A if this expression is of form []<>A. */
	public LiveExprNode getAEBody() {
		return null;
	}

	/* Return A if this expression is of form <>[]A. */
	public LiveExprNode getEABody() {
		return null;
	}

	/**
	 * Return true if this expression is a general temporal formula containing
	 * no []<>A or <>[]A.
	 */
	public boolean isGeneralTF() {
		return true;
	}

	/* This method pushes a negation all the way down to the atoms. */
	public LiveExprNode pushNeg() {
		// for the remaining types, simply negate:
		return new LNNeg(this);
	}

	/**
	 * This method pushes a negation all the way down to the atoms. It is
	 * currently not used.
	 */
	public LiveExprNode pushNeg(boolean hasNeg) {
		if (hasNeg) {
			return new LNNeg(this);
		}
		return this;
	}


	/**
	 * The method simplify does some simple simplifications before starting any
	 * real work. It will get rid of any boolean constants (of type LNBool).
	 */
	public LiveExprNode simplify() {
		// for the remaining types, simply negate:
		return this;
	}
	
	/**
	 * The method toDNF turns a LiveExprNode into disjunctive normal form.
	 */
	public LiveExprNode toDNF() {
		// For the remaining types, there is nothing to do:
		return this;
	}

	/**
	 * This method eliminates (flattens) singleton conjunctions and
	 * disjunctions. For example, /\[single-thing] is rewritten to single-thing.
	 * Note: With the current version of toDNF, there is probably no need for
	 * calling this method.
	 */
	public LiveExprNode flattenSingleJunctions() {
		// Finally, for the remaining types, there is nothing to do:
		return this;
	}

	/**
	 * This method makes all conjunctions and disjunctions binary. This is for
	 * tableau 'triple' construction. We'll do a recursive thing to balance the
	 * binary trees. Note that there can be no LNActions.
	 */
	public LiveExprNode makeBinary() {
		return this;
	}

	/**
	 * TagExpr tags all Act and State subexpressions in an expression. It
	 * returns the maximum tag used so that the caller can proceed with other
	 * tags in its depth-first traversal.
	 */
	public int tagExpr(int tag) {
		return tag;
	}

	/**
	 * The method extractPromises, given a formula, returns all the promises in
	 * its closure. All promises are in the form <>p. (We assume that we have
	 * pushed all negations inside. So, there are no -[]ps.) The closure of a
	 * formula says: for all subformulas of p, they are also in the closure. And
	 * some other rules, none of which have the possibility of creating a
	 * promise! So we only need look at subformulas of p.
	 */
	public void extractPromises(TBPar promises) {
		// Finally, for the remaining kinds, there is nothing to do.
		return;
	}

	public String toDotViz() {
		// By default just return the regular toString rep.
		return toString();
	}
}
