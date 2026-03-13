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
 * <h3>Relationship to the tableau</h3>
 * The PEM is a <em>decomposition</em> of the negated liveness formula that
 * exploits the mathematical structure of {@code []<>} and {@code <>[]} over
 * omega-regular cycles.  In the standard Vardi-Wolper / Manna-Pnueli approach,
 * the <em>entire</em> negated property is translated into a Büchi automaton:
 * every {@code []<>P} conjunct adds automaton nodes (tracking "waiting for P"
 * vs "P just seen") and an acceptance set, and every {@code <>[]E} conjunct
 * adds structure to track whether E has become permanently true.  Each such
 * conjunct enlarges the tableau and, because the product graph has size
 * |states| × |tableau nodes|, directly inflates memory and SCC analysis cost.
 * <p>
 * TLC instead extracts top-level {@code []<>} and {@code <>[]} conjuncts from
 * the negated formula and stores them in the PEM, leaving only the "complex"
 * temporal structure (nested eventualities such as {@code <>(P /\ <>Q)},
 * counting sequences, etc.) in the tableau.  The extracted conditions have
 * trivial characterizations over SCCs:
 * <ul>
 * <li>{@code []<>S} (AEState) holds on a lasso iff S holds at some state in
 *     the cycle (the cycle repeats forever, so S recurs infinitely often).</li>
 * <li>{@code []<>A} (AEAction) holds iff A fires on some transition in the
 *     cycle.</li>
 * <li>{@code <>[]E} (EAAction) holds iff E holds on <em>every</em> transition
 *     in the cycle (once inside the cycle, E holds permanently).</li>
 * </ul>
 * These are evaluated as simple predicates during
 * {@link LiveWorker#checkComponent()} rather than being tracked as automaton
 * states, keeping the tableau small and SCC analysis fast.
 * <p>
 * <h3>Fairness and property conditions in the same PEM</h3>
 * TLC checks {@code Spec => Property} by searching for behaviors satisfying
 * {@code Spec /\ ~Property}.  Both the fairness constraints (from Spec) and the
 * negated property can contribute conditions to the PEM:
 * <ul>
 * <li><b>Fairness → AEAction / EAAction:</b>  {@code WF_v(A)} expands to
 *     {@code []<><<A>>_v \/ <>[]~ENABLED<<A>>_v}, contributing an AEAction and
 *     an EAAction conjunct.  {@code SF_v(A)} similarly contributes an EAAction
 *     and an AEAction conjunct.</li>
 * <li><b>Property negation → AEState / AEAction / EAAction:</b>  If the
 *     property is {@code <>[]P}, its negation {@code []<>~P} becomes an
 *     AEState entry.  Properties like {@code []<><<A>>_v} contribute AEAction
 *     upon negation.</li>
 * </ul>
 * Because the PEM is a <em>conjunction</em>, a cycle (SCC) is only a valid
 * counter-example when <em>all</em> conditions hold simultaneously: the
 * behavior must be fair (honoring the spec's fairness constraints) <em>and</em>
 * the property must be genuinely violated.  This is critical: without the
 * fairness conditions in the PEM, TLC could report counter-examples on unfair
 * behaviors that are not valid behaviors of the spec.
 * <p>
 * <h3>Theory</h3>
 * A {@link PossibleErrorModel} (there are as many PEMs as
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

	/**
	 * Check whether this PEM's conditions are satisfied by infinite stuttering at
	 * the state whose check results are given. On a stuttering tail (s, s, s, ...):
	 * <ul>
	 * <li>[]<>S (AEState) holds iff S(s) is true (state never changes)</li>
	 * <li>[]<>A (AEAction) holds iff A(s,s) is true (every step is (s,s))</li>
	 * <li><>[]E (EAAction) holds iff E(s,s) is true (E holds forever trivially)</li>
	 * </ul>
	 *
	 * @param checkStateRes  result of evaluating all state predicates at s
	 * @param checkActionRes result of evaluating all action predicates on (s, s)
	 */
	public final boolean isSatisfiedByStuttering(boolean[] checkStateRes, BitVector checkActionRes) {
		for (int i = 0; i < AEState.length; i++) {
			if (!checkStateRes[AEState[i]]) {
				return false;
			}
		}
		for (int i = 0; i < AEAction.length; i++) {
			if (!checkActionRes.get(AEAction[i])) {
				return false;
			}
		}
		for (int i = 0; i < EAAction.length; i++) {
			if (!checkActionRes.get(EAAction[i])) {
				return false;
			}
		}
		return true;
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
