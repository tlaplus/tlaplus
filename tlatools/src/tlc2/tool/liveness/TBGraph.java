// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:50 PST by lamport
//      modified on Thu Sep 21 12:05:08 PDT 2000 by yuanyu

package tlc2.tool.liveness;

import tlc2.util.Vect;

public class TBGraph extends Vect {
	/**
	 * TBGraph represents the nodes in the tableau graph.
	 */
	public final LiveExprNode tf;
	private int initCnt;

	public TBGraph(LiveExprNode tf) {
		this.tf = tf;
		this.initCnt = 0;
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
				sb.append(tnode.nextAt(j).index + " ");
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
