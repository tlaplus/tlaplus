// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:50 PST by lamport
//      modified on Sun Aug  5 00:16:15 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tla2sany.semantic.LevelConstants;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.util.SetOfLong;
import tlc2.util.Vect;

public class TBGraphNode {
	/**
	 * TBGraphNode represents a node in the tableau graph. Read MP for what a
	 * particle tableau graph is. We give each node in the tableau-graph an
	 * index because it might be useful for hashing. statePreds are deduced from
	 * the particle at the moment of creation. They are later used in checking
	 * if a state-node is consistent with a tableau-node.
	 */
	private final TBPar par; // particle
	public final Vect<TBGraphNode> nexts; // outlinks
	private int index; // unique id for this node
	private final LiveExprNode[] statePreds; // state predicates in the particle


	public TBGraphNode(TBPar par) {
		this.par = par;
		this.index = 0;
		this.nexts = new Vect<>();
		TBPar preds = new TBPar(par.size());
		for (int i = 0; i < par.size(); i++) {
			LiveExprNode ln = par.exprAt(i);
			// MAK 04/15/2021: See MAK 04/15/2021 notes in comment of
			// tlc2.tool.liveness.LiveExprNode.simplify().
			// The conditional below has been changed in two dimension:
			// a) Instead of checking the concrete ln's type with instanceof, we check the
			// ln's level.
			// b) The check has been changed to accept ConstantLevel *and* VariableLevel,
			// which used to be just VariableLevel.
			// Obviously, constant-level expressions may appear in places where
			// VariableLevel (state-level) expressions are allowed. Ignoring a
			// constant-level expression here, causes bogus counterexamples reported for
			// properties such as `<>TRUE` or `FALSE ~> x#x` (see Github604.tla/java for
			// more details). Widening the check below to include constant-level expressions
			// causes additional state predicates to be created. If one of more of those
			// state predicates evaluate to false for a given state in
			// tlc2.tool.liveness.TBGraphNode.isConsistent(TLCState, ITool), the state gets
			// excluded from the behavior graph.
			// The assertion with msg "Found LNAction(s) in temporal formulae." in
			// Liveness.java implies that the LiveExprNode sub-types that we can encounter
			// here won't include LNActions. The comment of
			// tlc2.tool.liveness.TBPar.positiveClosure() confirms it too.
			// However, ln.getLevel might still be action or temporal because of e.g. formulae
			// such as `[]~someStatePredicate` as negation of `<>someStatePredicate`, or
			// `()[]~(someStatePredicate)` as a particle of `[]-someStatePredicate` with `()`
			// denoting LNNext/LTL's next operator.
			if (ln.getLevel() <= LevelConstants.VariableLevel) {
				preds.addElement(ln);
			}
		}
		this.statePreds = new LiveExprNode[preds.size()];
		for (int i = 0; i < preds.size(); i++) {
			this.statePreds[i] = preds.exprAt(i);
		}
	}

	public int getIndex() {
		return index;
	}

	public void setIndex(final int i) {
		this.index = i;
	}

	public final TBPar getPar() {
		return this.par;
	}

	public int nextSize() {
		return this.nexts.size();
	}

	public TBGraphNode nextAt(int i) {
		return (TBGraphNode) this.nexts.elementAt(i);
	}

	public final boolean hasLink(TBGraphNode target) {
		int sz = this.nexts.size();
		for (int i = 0; i < sz; i++) {
			if (this.nexts.elementAt(i) == target) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Checks if this particle node is consistent with the given
	 * {@link TLCState}. In other words, it checks if {@link TLCState}'s truth
	 * values according to all state predicates of the tableau node. The state
	 * predicates are deduced from the particles during tableau construction.
	 */
	public boolean isConsistent(TLCState state, ITool tool) {
		for (int j = 0; j < this.statePreds.length; j++) {
			if (!this.statePreds[j].eval(tool, state, null)) {
				return false;
			}
		}
		return true;
	}
	
	private final boolean isSelfLoop() {
		if (nextSize() == 1) {
			return nextAt(0) == this;
		}
		return false;
	}
	
	public final boolean isAccepting() {
		if (par.isEmpty() && isSelfLoop()) {
			return true;
		}
		return false;
	}

	public final String toString() {
		StringBuffer buf = new StringBuffer();
		SetOfLong visited = new SetOfLong(16);
		this.toString(buf, visited);
		return buf.toString();
	}

	private final void toString(StringBuffer buf, SetOfLong visited) {
		if (!visited.put(this.index)) {
			buf.append(this.par.toString());
			for (int i = 0; i < this.nexts.size(); i++) {
				buf.append(this.nextAt(i).index + " ");
			}
			buf.append("\n");
			for (int i = 0; i < this.nexts.size(); i++) {
				this.nextAt(i).toString(buf, visited);
			}
		}
	}

	/**
	 * @see TBGraph#toDotViz()
	 */
	public String toDotViz(final boolean isInitNode) {
		final String label = "\"Id: " + this.index + "\n" + par.toDotViz() + "\"";
		
		final StringBuffer buf = new StringBuffer(nextSize());
		buf.append(this.index + " [label=" + label + "]\n"); // nodes label
		if (isInitNode) {
			buf.append("[style = filled]\n");
		}
		for (int i = 0; i < nextSize(); i++) {
			final TBGraphNode successor = nextAt(i);
			buf.append(this.index + " -> " + successor.index);
			buf.append("\n");
		}
		return buf.toString();
	}
}

