// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:50 PST by lamport
//      modified on Thu Sep 21 12:05:08 PDT 2000 by yuanyu

package tlc2.tool.liveness;

import tlc2.util.Vect;

@SuppressWarnings("serial")
public class TBGraph extends Vect {
	/**
	 * TBGraph represents the nodes in the tableau graph.
	 */
	public final LiveExprNode tf;
	private int initCnt;

	public TBGraph() {
		this.tf = null;
		this.initCnt = 0;
	}

	/**
	 * Given a starting TBGraphNode, constructTableau constructs the tableau for
	 * it. Read MP for details. It returns a list of all the nodes in the
	 * tableau graph.
	 */
	public TBGraph(final LiveExprNode tf) {
		this.tf = tf;
		this.initCnt = 0;
		
		final TBPar initTerms = new TBPar(1);
		initTerms.addElement(tf);
		final TBParVec pars = initTerms.particleClosure();

		for (int i = 0; i < pars.size(); i++) {
			final TBGraphNode gn = new TBGraphNode(pars.parAt(i));
			this.addElement(gn);
		}
		this.setInitCnt(this.size());
		// We now repeatedly compute the outlinks of each node:
		for (int i = 0; i < this.size(); i++) {
			final TBGraphNode gnSrc = (TBGraphNode) this.elementAt(i);
			final TBPar imps = gnSrc.getPar().impliedSuccessors();
			final TBParVec succs = imps.particleClosure();
			for (int j = 0; j < succs.size(); j++) {
				final TBPar par = succs.parAt(j);
				final TBGraphNode gnDst = findOrCreateNode(par);
				gnSrc.nexts.addElement(gnDst);
			}
		}
		// Assign each node in the tableau an index.
		for (int i = 0; i < this.size(); i++) {
			this.getNode(i).setIndex(i);
		}
	}
	
	/**
	 * The method findOrCreateNode, given a list of particles, either finds the
	 * particle in that list, or creates a new one and puts it in the list. If
	 * it does create a node, then it also sticks that node into allnodes.
	 */
	private TBGraphNode findOrCreateNode(final TBPar par) {
		for (int i = 0; i < this.size(); i++) {
			final TBGraphNode gn = (TBGraphNode) this.elementAt(i);
			if (par.equals(gn.getPar())) {
				return gn;
			}
		}
		final TBGraphNode gn = new TBGraphNode(par);
		this.addElement(gn);
		return gn;
	}

	public TBGraphNode getNode(int idx) {
		return (TBGraphNode) this.elementAt(idx);
	}

	public final void setInitCnt(int n) {
		this.initCnt = n;
	}

	public int getInitCnt() {
		return this.initCnt;
	}

	public final void toString(StringBuffer sb, String padding) {
		for (int i = 0; i < this.size(); i++) {
			TBGraphNode tnode = this.getNode(i);
			sb.append(padding);
			sb.append("Node " + i + ".\n");
			tnode.getPar().toString(sb, padding);
			sb.append(" --> ");
			for (int j = 0; j < tnode.nexts.size(); j++) {
				sb.append(tnode.nextAt(j).getIndex() + " ");
			}
			sb.append("\n");
		}
	}

	public final String toString() {
		StringBuffer sb = new StringBuffer();
		this.toString(sb, "");
		return sb.toString();
	}

	/**
	 * @see AbstractDiskGraph#toDotViz()
	 */
	public String toDotViz() {
		final StringBuffer sb = new StringBuffer();
		sb.append("digraph TableauGraph {\n");
		sb.append("nodesep = 0.7\n");
		sb.append("rankdir=LR;\n"); // Left to right rather than top to bottom
		for(int i = 0; i < size(); i++) {
			sb.append(getNode(i).toDotViz());
		}
		sb.append("}");
		return sb.toString();
	}
}
