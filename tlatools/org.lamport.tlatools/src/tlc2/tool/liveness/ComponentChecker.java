/*******************************************************************************
 * Copyright (c) 2026 Microsoft Research. All rights reserved.
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ******************************************************************************/
package tlc2.tool.liveness;

import java.io.IOException;

/**
 * Checks if a strongly connected component (SCC) of the liveness graph
 * satisfies a {@link PossibleErrorModel} (PEM), i.e. contains a
 * counterexample.
 * <p>
 * An instance only reads its {@link OrderOfSolution} and
 * {@link PossibleErrorModel}, and is thus safe to be used by multiple threads
 * as long as each thread passes its own {@link NodeSource} and
 * {@link Result}.
 */
final class ComponentChecker {

	@FunctionalInterface
	interface NodeSource {
		GraphNode getNode(long stateFP, int tidx, long ptr) throws IOException;
	}

	@FunctionalInterface
	interface Members {
		boolean contains(long stateFP, int tidx);
	}

	/**
	 * Which of the PEM's AEStates, AEActions, and promises are satisfied by (a
	 * subset of) the nodes of an SCC.
	 */
	final class Result {
		private final boolean[] aeState = new boolean[pem.AEState.length];
		private final boolean[] aeAction = new boolean[pem.AEAction.length];
		private final boolean[] promise = new boolean[oos.getPromises().length];

		/**
		 * We find a counterexample if all three conditions are satisfied. If
		 * either of the conditions is false, it means the PEM does not hold and
		 * thus the liveness properties are not violated by the SCC.
		 * <p>
		 * All AEState properties, AEActions and promises of PEM must be
		 * satisfied. If a single one isn't satisfied, the PEM as a whole isn't
		 * P-satisfiable. EAAction have already been checked by the SCC search
		 * (which only follows transitions that satisfy the EAAction).
		 */
		boolean isCounterExample() {
			for (int i = 0; i < aeState.length; i++) {
				if (!aeState[i]) {
					return false;
				}
			}
			for (int i = 0; i < aeAction.length; i++) {
				if (!aeAction[i]) {
					return false;
				}
			}
			for (int i = 0; i < promise.length; i++) {
				if (!promise[i]) {
					return false;
				}
			}
			return true;
		}
	}

	private final OrderOfSolution oos;
	private final PossibleErrorModel pem;
	private final int slen;
	private final int alen;

	ComponentChecker(final OrderOfSolution oos, final PossibleErrorModel pem) {
		this.oos = oos;
		this.pem = pem;
		this.slen = oos.getCheckState().length;
		this.alen = oos.getCheckAction().length;
	}

	Result newResult() {
		return new Result();
	}

	/**
	 * @return true iff the node has a self loop that satisfies the PEM's
	 *         EAAction (the node stutters).
	 */
	boolean isStuttering(final GraphNode gnode) {
		final long state = gnode.stateFP;
		final int tidx = gnode.tindex;
		// Find the self loop and check its <>[]action
		final int succCnt = gnode.succSize();
		for (int i = 0; i < succCnt; i++) {
			final long nextState = gnode.getStateFP(i);
			final int nextTidx = gnode.getTidx(i);
			if (state == nextState && tidx == nextTidx) {
				return gnode.getCheckAction(slen, alen, i, this.pem.EAAction);
			}
		}
		// <state, tidx> has no self loop, thus cannot stutter
		return false;
	}

	/**
	 * @return true iff the whole SCC com violates liveness.
	 * @see #check(TableauNodePtrTable, int, int, NodeSource, Result)
	 */
	boolean isCounterExample(final TableauNodePtrTable com, final NodeSource source) throws IOException {
		final Result res = newResult();
		check(com, 0, com.getSize(), source, res);
		return res.isCounterExample();
	}

	/**
	 * Accumulates into res which of the PEM's AEStates, AEActions, and
	 * promises are satisfied by the nodes of the SCC com that are in com's
	 * buckets [fromLoc, toLoc). Iterating all buckets [0, com.getSize())
	 * checks the whole SCC.
	 * <p>
	 * Speaking in words of Manna & Pnueli (Page 422ff), it checks if ~&#966;
	 * (which is PEM) is "P-satisfiable" (i.e. is there a computation that
	 * satisfies &#968;). ~&#966; (called &#968; by MP) is the negation of the
	 * liveness formula &#966; which has to be "P-valid" for the liveness
	 * properties to be valid.
	 *
	 */
	void check(final TableauNodePtrTable com, final int fromLoc, final int toLoc, final NodeSource source,
			final Result res) throws IOException {
		final Members members = (fp, tidx) -> com.getLoc(fp, tidx) != -1;

		// Extract a node from the nodePtrTable "com".
		// Note the upper limit is NodePtrTable#getSize() instead of
		// the more obvious NodePtrTable#size().
		// NodePtrTable internally hashes the elements to buckets
		// and isn't filled start to end. Thus, the code
		// below iterates NodePtrTable front to end skipping null buckets.
		//
		// Note that the nodes are processed in random order (depending on a
		// node's hash in TableauNodePtrTbl) and not in the order given by
		// comStack. This is fine because the all checks have been evaluated
		// eagerly during insertion into the liveness graph long before the
		// SCC search started. Thus, the code here only has to check the
		// check results which can happen in any order.
		for (int ci = fromLoc; ci < toLoc; ci++) {
			final int[] nodes = com.getNodesByLoc(ci);
			if (nodes == null) {
				// miss in NotePtrTable (null bucket)
				continue;
			}

			final long state1 = TableauNodePtrTable.getKey(nodes);
			for (int nidx = 2; nidx < nodes.length; nidx += com.getElemLength()) { // nidx starts with 2 because [0][1] are the long fingerprint state1.
				final int tidx1 = TableauNodePtrTable.getTidx(nodes, nidx);
				final long loc1 = TableauNodePtrTable.getElem(nodes, nidx);

				check(source.getNode(state1, tidx1, loc1), members, res);
			}
		}
	}

	/**
	 * Accumulates into res which of the PEM's AEStates, AEActions, and
	 * promises are satisfied by curNode, a node of the SCC com.
	 */
	void check(final GraphNode curNode, final Members com, final Result res) {
		final int aeslen = this.pem.AEState.length;
		final int aealen = this.pem.AEAction.length;
		final int plen = this.oos.getPromises().length;
		final boolean[] AEStateRes = res.aeState;
		final boolean[] AEActionRes = res.aeAction;
		final boolean[] promiseRes = res.promise;
		final int[] eaaction = this.pem.EAAction;

		// Check AEState:
		for (int i = 0; i < aeslen; i++) {
			// Only ever set AEStateRes[i] to true, but never to false
			// once it was true. It only matters if one state in com
			// satisfies PEM's liveness property due to []<>~p (which is
			// the inversion of <>[]p).
			//
			// It obviously has to check all nodes in the component
			// (com) if either of them violates AEState unless all
			// elements of AEStateRes are true. From that point onwards,
			// checking further states wouldn't make a difference.
			if (!AEStateRes[i]) {
				int idx = this.pem.AEState[i];
				AEStateRes[i] = curNode.getCheckState(idx);
				// Can stop checking AEStates the moment AEStateRes
				// is completely set to true. However, most of the time
				// aeslen is small and the compiler will probably optimize
				// out.
			}
		}

		// Check AEAction: A TLA+ action represents the relationship
		// between the current node and a successor state. The current
		// node has n successor states. For each pair, see iff the
		// successor is in the "com" NodePtrTablecheck, check actions
		// and store the results in AEActionRes(ult). Note that the
		// actions have long been checked in advance when the node was
		// added to the graph and the actual state and not just its
		// fingerprint was available. Here, the result is just being
		// looked up.
		final int succCnt = aealen > 0 ? curNode.succSize() : 0; // No point in looping successors if there are no AEActions to check on them.
		for (int i = 0; i < succCnt; i++) {
			final long nextState = curNode.getStateFP(i);
			final int nextTidx = curNode.getTidx(i);
			// For each successor <<nextState, nextTdix>> of curNode's
			// successors check, if it is part of the currently
			// processed SCC (com). Successors, which are not part of
			// the current SCC have obviously no relevance here. After
			// all, we check the SCC.
			if (!com.contains(nextState, nextTidx)) {
				continue;
			}
			// MAK 10/23/2018:
			// Line 380 above "if(gnode.getCheckAction)" causes a transition A from state s
			// -> t to be skipped even if a belongs to an SCC iff the transition A does not
			// satisfy the EA action of the PossibleErrorModel (if the EA action(s) is not
			// satisfied, the PEM cannot hold at all).
			// However, some state graphs are such that there exists not just the transition
			// A from s -> t but a second transition A' from t -> s - which satisfies the EA
			// action(s) of the PEM. In the case of a "bidirectional" transition, the states
			// s and t will be in the set of states 'com' (which make up the SCC). Thus, the
			// transition A from s -> t will be incorrectly traversed here unless it is
			// skipped (again). Not skipping the transition A will result in TLC reporting a
			// (bogus) counterexample even if the liveness is not violated.
			//
			// Consider the spec BT for which TLC incorrectly reports a liveness property
			// violation and prints a bogus counterexample:
			//
			// ---- BT -----
			// EXTENDS Naturals
			// VARIABLE x
			// A == \/ x' = (x + 1) % 3
			// B == x' \in 0..2
			// Spec == (x=0) /\ [][A \/ B]_x/\ WF_x(A)
			// Prop == Spec /\ WF_x(A) /\ []<><<A>>_x
			// =============
			//
			// > Temporal properties were violated.
			// > The following behavior constitutes a counter-example:
			// > 1: <Initial predicate>
			// > x = 0
			// > 2: <A line xx...BT>
			// > x = 1
			// > 1: Back to state: <B line xx... BT>
			//
			// (see tlc2.tool.BidirectionalTransitions1Test and BidirectionalTransitions2Test)
			if(!curNode.getCheckAction(slen, alen, i, eaaction)) {
				continue;
			}
			for (int j = 0; j < aealen; j++) {
				// Only set false to true, but never true to false.
				if (!AEActionRes[j]) {
					final int idx = this.pem.AEAction[j];
					AEActionRes[j] = curNode.getCheckAction(slen, alen, i, idx);
				}
			}
		}

		// Check that the component is fulfilling. (See MP page 453.)
		// Note that the promises are precomputed and stored in oos.
		for (int i = 0; i < plen; i++) {
			final LNEven promise = this.oos.getPromises()[i];
			final TBPar par = curNode.getTNode(this.oos.getTableau()).getPar();
			if (par.isFulfilling(promise)) {
				promiseRes[i] = true;
			}
		}
	}
}
