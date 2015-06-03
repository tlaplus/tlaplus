// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:49 PST by lamport
//      modified on Fri Jul 14 15:40:49 PDT 2000 by yuanyu

package tlc2.tool.liveness;

import java.io.PrintStream;

import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.BitVector;

/*
 * Roughly speaking, each temporal formula maps 1:1 to OrderOfSolution. Say TLC is set to check
 * the three temporal formulas A, B, C, there will be three OrderOfSolution instances 
 * (one for each of formula). More precisely, each conjunct is represented by an OOS.
 * 
 * For details, see page 405 to 408 of "Temporal verification of Reactive Systems * safety *"
 * by Manna and Pnueli (abbreviated to "MP book" in most of TLC's code comments).
 *  
 * Note that TLC does *not* check if A, B or C are identical formulas. If TLC is set to
 * check A, A, A (it will still create three OrderOfSolutions). It is up to the
 * user to prevent this.
 */
public class OrderOfSolution {
	/**
	 * The algorithm will decompose the fairness spec /\ ~check into a
	 * disjunction of conjuncts of the following form: (<>[]a /\ []<>b /\ tf1)
	 * \/ (<>[]c /\ []<>d /\ tf2) .. For efficiency, we will identify disjuncts
	 * that have the same tableau (tf), and OrderOfSolution groups them
	 * together: (<>[]a/\[]<>b \/ <>[]c/\[]<>d) /\ tf Each conjunct
	 * (<>[]a/\[]<>b) is represented by a PossibleErrorModel. The solution then
	 * proceeds: construct the behaviour graph using the tableau, compute
	 * strongly connected components, and see if it meets any one of the
	 * disjunctions. Also, it's likely that a single order of solution will have
	 * lots of duplication in its <>[] and []<> spread over its disjunctions and
	 * conjunctions. To avoid waste, we use a lookup table: checkState,
	 * checkAction: when examining each state and its transitions, these are the
	 * things we have to remember before throwing it away. The possible error
	 * model stores indexes into checkState and checkAction arrays, under EA/AE,
	 * state/action. The field promises are all the promises contained in the
	 * closure.
	 */

	/*
	 * The size of the tableau graph is a function of the amount of disjuncts
	 * in the temporal formulas.
	 */
	private final TBGraph tableau; // tableau graph
	
	/**
	 * A promise &#966; that a property expressed by a formula will eventually hold.
	 * 
	 * @see Page 409ff of Manna & Pnueli
	 * "Temporal Verification of Reactive Systems: Safety"
	 * <p>
	 * @see https://books.google.de/books?id=lfIGCAAAQBAJ&lpg=PR5&ots=_YBX09o5tM
	 *      &dq=manna%20pnueli%20temporal%20verification%20of%20reactive%
	 *      20systems%20safety%20doi&pg=PA409
	 */
	private final LNEven[] promises; // promises in the tableau
	private LiveExprNode[] checkState; // state subformula
	private LiveExprNode[] checkAction; // action subformula
	private PossibleErrorModel[] pems;
	private final Tool tool;

	public OrderOfSolution(final LNEven[] livenessEventually, Tool aTool) {
		this(null, livenessEventually, aTool);
	}

	public OrderOfSolution(final TBGraph aTableau, final LNEven[] livenessEventually, Tool aTool) {
		tableau = aTableau;
		promises = livenessEventually;
		this.tool = aTool;
	}

	public final void printPromises(PrintStream ps) {
		for (int i = 0; i < this.getPromises().length; i++) {
			ps.println(this.getPromises()[i].toString());
		}
	}

	public final String toString() {
		if (this.getPems().length == 0) {
			return "";
		}
		StringBuffer sb = new StringBuffer();
		this.toString(sb);
		return sb.toString();
	}

	public final void toString(StringBuffer sb) {
		String padding = "";
		int plen = this.getPems().length;

		if (this.hasTableau()) {
			if (plen == 1 && this.getPems()[0].isEmpty()) {
				this.getTableau().tf.toString(sb, "   ");
				return;
			} else {
				sb.append("/\\ ");
				this.getTableau().tf.toString(sb, "   ");
				sb.append("\n/\\ ");
				padding = "   ";
			}
		}

		if (plen == 1) {
			this.getPems()[0].toString(sb, padding, checkState, this.getCheckAction());
		} else {
			sb.append("\\/ ");
			String padding1 = padding + "   ";
			this.getPems()[0].toString(sb, padding1, checkState, this.getCheckAction());
			for (int i = 1; i < plen; i++) {
				sb.append(padding + "\\/ ");
				this.getPems()[i].toString(sb, padding1, checkState, this.getCheckAction());
			}
		}
	}

	public TBGraph getTableau() {
		return tableau;
	}

	public boolean hasTableau() {
		return tableau != null;
	}

	public LNEven[] getPromises() {
		return promises;
	}

	public LiveExprNode[] getCheckState() {
		return checkState;
	}
	
	public boolean[] checkState(final TLCState state) {
		final boolean[] result = new boolean[checkState.length];
		for (int i = 0; i < checkState.length; i++) {
			result[i] = checkState[i].eval(tool, state, null);
		}
		return result;
	}

	void setCheckState(LiveExprNode[] checkState) {
		this.checkState = checkState;
	}

	// legacy LiveCheck1
	public boolean[] checkAction(final TLCState state0, final TLCState state1) {
		final boolean[] result = new boolean[checkAction.length];
		for (int i = 0; i < checkAction.length; i++) {
			result[i] = checkAction[i].eval(tool, state0, state1);
		}
		return result;
	}
	
	public BitVector checkAction(final TLCState state0, final TLCState state1, final BitVector result, final int offset) {
		for (int i = 0; i < checkAction.length; i++) {
			if (checkAction[i].eval(tool, state0, state1)) {
				result.set(offset + i);
			}
		}
		return result;
	}
	
	public LiveExprNode[] getCheckAction() {
		return checkAction;
	}

	void setCheckAction(LiveExprNode[] checkAction) {
		this.checkAction = checkAction;
	}

	public PossibleErrorModel[] getPems() {
		return pems;
	}

	void setPems(PossibleErrorModel[] pems) {
		this.pems = pems;
	}

}
