// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:49 PST by lamport
//      modified on Fri Jul 14 15:40:49 PDT 2000 by yuanyu

package tlc2.tool.liveness;

import java.io.PrintStream;

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
	 * The size of the tableaux graph is a function of the amount of 
	 * disjuncts in the temporal formuals.
	 */
	public TBGraph tableau; // tableau graph
	public LNEven[] promises; // promises in the tableau
	public LiveExprNode[] checkState; // state subformula
	public LiveExprNode[] checkAction; // action subformula
	public PossibleErrorModel[] pems;

	public final void printPromises(PrintStream ps) {
		for (int i = 0; i < this.promises.length; i++) {
			ps.println(this.promises[i].toString());
		}
	}

	public final String toString() {
		if (this.pems.length == 0) {
			return "";
		}
		StringBuffer sb = new StringBuffer();
		this.toString(sb);
		return sb.toString();
	}

	public final void toString(StringBuffer sb) {
		String padding = "";
		int plen = this.pems.length;

		if (this.tableau != null) {
			if (plen == 1 && this.pems[0].isEmpty()) {
				this.tableau.tf.toString(sb, "   ");
				return;
			} else {
				sb.append("/\\ ");
				this.tableau.tf.toString(sb, "   ");
				sb.append("\n/\\ ");
				padding = "   ";
			}
		}

		if (plen == 1) {
			this.pems[0].toString(sb, padding, this.checkState, this.checkAction);
		} else {
			sb.append("\\/ ");
			String padding1 = padding + "   ";
			this.pems[0].toString(sb, padding1, this.checkState, this.checkAction);
			for (int i = 1; i < plen; i++) {
				sb.append(padding + "\\/ ");
				this.pems[i].toString(sb, padding1, this.checkState, this.checkAction);
			}
		}
	}

}
