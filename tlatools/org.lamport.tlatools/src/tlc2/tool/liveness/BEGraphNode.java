// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:36 PST by lamport
//      modified on Mon Nov 26 14:28:11 PST 2001 by yuanyu

package tlc2.tool.liveness;

import util.WrongInvocationException;

import java.util.BitSet;

public class BEGraphNode extends AbstractGraphNode {
    private static final BEGraphNode[] emptyNodes = new BEGraphNode[0];
    /**
     * BEGraphNode is a node in the behaviour graph. We're going to only store
     * fingerprints of states, rather than actual states. So, as we encounter
     * each state, we will calculate all the <>[] and []<>s listed in our order
     * of solution. For each arrow we must record the target node and the
     * checkActions along it.
     */
    public final long stateFP; // fingerprint of the state
    private BEGraphNode[] nnodes; // outgoing links
    private long number; // for DFS and SCC

    public BEGraphNode(final long fp) {
        super(new BitSet(0));
        this.stateFP = fp;
        this.nnodes = emptyNodes;
        this.number = 0;
    }

    public final long resetNumberField() {
        final long old = this.number;
        this.number = 0;
        return old;
    }

    public final long getNumber() {
        return (this.number & 0x7FFFFFFFFFFFFFFFL);
    }

    public final void setNumber(final long num) {
        this.number = (this.number < 0) ? (num | 0x8000000000000000L) : num;
    }

    public final void incNumber() {
        this.number++;
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
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (getClass() != obj.getClass()) {
            return false;
        }
        final BEGraphNode other = (BEGraphNode) obj;
        return stateFP == other.stateFP;
    }

    public final BEGraphNode nextAt(final int i) {
        return this.nnodes[i];
    }

    public final int nextSize() {
        return this.nnodes.length;
    }

    public final void addTransition(final BEGraphNode target, final int slen, final int alen, final boolean[] acts) {
        final int num = this.nnodes.length;
        if (acts != null) {
            final int pos = slen + alen * num;
            for (int i = 0; i < acts.length; i++) {
                if (acts[i]) {
                    this.checks.set(pos + i);
                }
            }
        }
        final BEGraphNode[] newNodes = new BEGraphNode[num + 1];
        System.arraycopy(this.nnodes, 0, newNodes, 0, num);
        newNodes[num] = target;
        this.nnodes = newNodes;
    }

    public final boolean transExists(final BEGraphNode target) {
        for (final BEGraphNode nnode : this.nnodes) {
            if (target.equals(nnode)) {
                return true;
            }
        }
        return false;
    }

    public TBGraphNode getTNode(final TBGraph tableau) {
        throw new WrongInvocationException("TLC bug: should never call BEGraphNode.getTNode().");
    }

    public String nodeInfo() {
        return Long.toString(this.stateFP);
    }

    public final BEGraphNode getParent() {
        return this.nnodes[0];
    }

    /**
     * Set node to be the parent of this. This would destroy the original graph.
     * Use with caution.
     */
    public final void setParent(final BEGraphNode node) {
        if (this.nnodes.length == 0) {
            this.nnodes = new BEGraphNode[1];
        }
        this.nnodes[0] = node;
    }

    /**
     * This method assumes that the visited field of all the nodes is set to the
     * same value. It flips the visited field. We use the high-order bit of
     * this.number as the visited bit.
     */
    public final String toString() {
        final StringBuilder buf = new StringBuilder();
        this.toString(buf, this.getVisited());
        return buf.toString();
    }

    protected void toString(final StringBuilder buf, final boolean unseen) {
        if (this.getVisited() == unseen) {
            this.flipVisited();
            buf.append(this.stateFP).append(" --> ");
            final int size = this.nnodes.length;
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
