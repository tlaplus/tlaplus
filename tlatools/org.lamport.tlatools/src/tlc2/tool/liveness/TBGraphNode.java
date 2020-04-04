// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:50 PST by lamport
//      modified on Sun Aug  5 00:16:15 PDT 2001 by yuanyu

package tlc2.tool.liveness;

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

	public static TBGraphNode dummyNode = new TBGraphNode();

	private TBGraphNode() {
		this.par = null;
		this.nexts = null;
		this.index = -1;
		this.statePreds = null;
	}

	public TBGraphNode(TBPar par) {
		this.par = par;
		this.index = 0;
		this.nexts = new Vect<>();
		TBPar preds = new TBPar(par.size());
		for (int i = 0; i < par.size(); i++) {
			LiveExprNode ln = par.exprAt(i);
			if (ln instanceof LNState) {
				preds.addElement(ln);
			} else if (ln instanceof LNNeg) {
				LiveExprNode body = ((LNNeg) ln).getBody();
				if (body instanceof LNState) {
					preds.addElement(ln);
				}
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

