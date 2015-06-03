// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:49 PST by lamport
//      modified on Sat Mar 25 22:39:46 PST 2000 by yuanyu

package tlc2.tool.liveness;

import tlc2.util.BitVector;

/**
 * A {@link PossibleErrorModel} is technically a lookup table into its
 * corresponding {@link OrderOfSolution} Eventually Always, Infinitely often
 * action checks and infinitely often state checks. The
 * {@link PossibleErrorModel} basically selects the set of checks stored in
 * {@link OrderOfSolution} that a relevant for this {@link PossibleErrorModel}.
 * The mapping is done by storing the integer index of the relevant
 * {@link OrderOfSolution} checks in EAAction, AEState and AEAction.
 * <p>
 * The integer index is used in two places: Lookup the set of relevant OOS
 * checks
 * <ul>
 * <li>When the states and transitions (see
 * {@link GraphNode#addTransition(long, int, int, int, BitVector, int, int)})
 * are evaluated during "normal" model checking the PEM index selects the set of
 * relevant OOS checks. The result of each check is stored in a per node
 * {@link BitVector} index again by the corresponding PEM mapping.</li>
 * <li>During liveness checking (see {@link LiveWorker#checkSccs()} when the
 * pre-computed check result is being looked up in the node's {@link BitVector}.
 * </li>
 * </ul>
 * <p>
 * This class can be seen as a C-like struct (PEM's method are all related to
 * OOS#toString).
 * <p>
 * <p>
 * Theorie-wise, a {@link PossibleErrorModel} (there are as many PEMs as
 * disjuncts in the normal form (DNF) produced by
 * {@link Liveness#processLiveness(tlc2.tool.Tool)}) represents the negation of
 * the stated liveness properties. It is then applied onto the discovered
 * strongly-connected-components in {@link LiveWorker#checkComponent()} to check
 * if the PEM is "P-satisfiable". If it is, it shows that a violation of the
 * original liveness properties has been found (meaning they can't be
 * "P-valid"). A counter-example can be created.
 * <p>
 * A simplified example:<br>
 * Suppose Spec has the (trivial) liveness property '&lt;&gt;[](x \in Nat)' (
 * "eventually the variable x is always a natural number") defined. This will
 * result in a PEM looking for a state such that x \notin Nat. If there exists
 * such a behavior (SCC), it would violate the liveness property.
 */
public class PossibleErrorModel {
	final int[] EAAction; // <>[]act's (Eventually Always actions) (Strong fairness)
	final int[] AEState; // []<>state's (Infinitely Often states)
	final int[] AEAction; // []<>act's (Infinitely Often actions) (Weak fairness)
	
	public PossibleErrorModel(int[] aeAction, int[] aeState, int[] eaAction) {
		this.AEAction = aeAction;
		this.AEState = aeState;
		this.EAAction = eaAction;
	}
	
	public final boolean isEmpty() {
		return (this.EAAction.length == 0 && this.AEState.length == 0 && this.AEAction.length == 0);
	}

	public final String toString(LiveExprNode[] checkState, LiveExprNode[] checkAction) {
		StringBuffer sb = new StringBuffer();
		this.toString(sb, "", checkState, checkAction);
		return sb.toString();
	}

	public final void toString(StringBuffer sb, String padding, LiveExprNode[] checkState, LiveExprNode[] checkAction) {
		boolean noPadding = true;
		String padding1 = padding + "       ";

		for (int i = 0; i < this.EAAction.length; i++) {
			int idx = this.EAAction[i];
			if (noPadding) {
				noPadding = false;
			} else {
				sb.append(padding);
			}
			sb.append("/\\ <>[]");
			checkAction[idx].toString(sb, padding1);
			sb.append("\n");
		}
		for (int i = 0; i < this.AEState.length; i++) {
			int idx = this.AEState[i];
			if (noPadding) {
				noPadding = false;
			} else {
				sb.append(padding);
			}
			sb.append("/\\ []<>");
			checkState[idx].toString(sb, padding1);
			sb.append("\n");
		}
		for (int i = 0; i < this.AEAction.length; i++) {
			int idx = this.AEAction[i];
			if (noPadding) {
				noPadding = false;
			} else {
				sb.append(padding);
			}
			sb.append("/\\ []<>");
			checkAction[idx].toString(sb, padding1);
			sb.append("\n");
		}
	}

}
