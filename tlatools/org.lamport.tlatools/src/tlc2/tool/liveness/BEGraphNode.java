// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:36 PST by lamport
//      modified on Mon Nov 26 14:28:11 PST 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.util.BitVector;
import util.WrongInvocationException;

public class BEGraphNode extends AbstractGraphNode {
	/**
	 * BEGraphNode is a node in the behaviour graph. We're going to only store
	 * fingerprints of states, rather than actual states. So, as we encounter
	 * each state, we will calculate all the <>[] and []<>s listed in our order
	 * of solution. For each arrow we must record the target node and the
	 * checkActions along it.
	 */
	public long stateFP; // fingerprint of the state
	private BEGraphNode[] nnodes; // outgoing links
	private long number; // for DFS and SCC

	private static final BEGraphNode[] emptyNodes = new BEGraphNode[0];

	public BEGraphNode(long fp) {
		super(new BitVector(0));
		this.stateFP = fp;
		this.nnodes = emptyNodes;
		this.number = 0;
	}

	public final long resetNumberField() {
		long old = this.number;
		this.number = 0;
		return old;
	}

	public final long getNumber() {
		return (this.number & 0x7FFFFFFFFFFFFFFFL);
	}

	public final void incNumber() {
		this.number++;
	}

	public final void setNumber(long num) {
		this.number = (this.number < 0) ? (num | 0x8000000000000000L) : num;
	}

	public final boolean getVisited() {
		return this.number < 0;
	}

	public final void flipVisited() {
		this.number = this.number ^ 0x8000000000000000L;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (int) (stateFP ^ (stateFP >>> 32));
		return result;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		BEGraphNode other = (BEGraphNode) obj;
		if (stateFP != other.stateFP) {
			return false;
		}
		return true;
	}

	public final BEGraphNode nextAt(int i) {
		return this.nnodes[i];
	}

	public final int nextSize() {
		return this.nnodes.length;
	}

	public final void addTransition(BEGraphNode target, int slen, int alen, boolean[] acts) {
		int num = this.nnodes.length;
		if (acts != null) {
			int pos = slen + alen * num;
			for (int i = 0; i < acts.length; i++) {
				if (acts[i]) {
					this.checks.set(pos + i);
				}
			}
		}
		BEGraphNode[] newNodes = new BEGraphNode[num + 1];
		System.arraycopy(this.nnodes, 0, newNodes, 0, num);
		newNodes[num] = target;
		this.nnodes = newNodes;
	}

	public final boolean transExists(BEGraphNode target) {
		int len = this.nnodes.length;
		for (int i = 0; i < len; i++) {
			if (target.equals(this.nnodes[i])) {
				return true;
			}
		}
		return false;
	}

	public TBGraphNode getTNode(TBGraph tableau) {
		throw new WrongInvocationException("TLC bug: should never call BEGraphNode.getTNode().");
	}

	public String nodeInfo() {
		return Long.toString(this.stateFP);
	}

	/**
	 * Set node to be the parent of this. This would destroy the original graph.
	 * Use with caution.
	 */
	public final void setParent(BEGraphNode node) {
		if (this.nnodes.length == 0) {
			this.nnodes = new BEGraphNode[1];
		}
		this.nnodes[0] = node;
	}

	public final BEGraphNode getParent() {
		return this.nnodes[0];
	}

	/**
	 * This method assumes that the visited field of all the nodes is set to the
	 * same value. It flips the visited field. We use the high-order bit of
	 * this.number as the visited bit.
	 */
	public final String toString() {
		StringBuffer buf = new StringBuffer();
		this.toString(buf, this.getVisited());
		return buf.toString();
	}

	protected void toString(StringBuffer buf, boolean unseen) {
		if (this.getVisited() == unseen) {
			this.flipVisited();
			buf.append(this.stateFP + " --> ");
			int size = this.nnodes.length;
			if (size != 0) {
				buf.append(this.nextAt(0).stateFP);
			}
			for (int i = 1; i < size; i++) {
				buf.append(", ");
				buf.append(this.nextAt(i).stateFP);
			}
			buf.append("\n");
			for (int i = 0; i < size; i++) {
				this.nextAt(i).toString(buf, unseen);
			}
		}
	}

}
