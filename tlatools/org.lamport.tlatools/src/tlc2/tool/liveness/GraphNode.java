// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:37 PST by lamport
//      modified on Mon Nov 26 15:46:11 PST 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.util.BitSetUtilities;
import tlc2.util.BufferedRandomAccessFile;

import java.io.IOException;
import java.util.BitSet;
import java.util.HashSet;
import java.util.Set;

public class GraphNode extends AbstractGraphNode {
    /**
     * The record size indicates the number of integers used by each transition
     * in the array of nnodes (2x32bit to keep the fp and 32bit to keep the tableau
     * idx).
     */
    private static final int NNODE_RECORD_SIZE = 3;
    /**
     * GraphNode is a node in the behaviour graph. We're going to only store
     * fingerprints of states, rather than actual states. So, as we encounter
     * each state, we need to calculate all the <>[] and []<>'s listed in the
     * order of solution. For each outgoing edge, we record the fingerprint of
     * the target node and the checkActions along it.
     * <p>
     * The field tidx is the unique index for the tableau graph node. If tindex
     * = -1, then there is no tableau. So, the maximum size of tableau is 2^31.
     */
    private static final int[] emptyIntArr = new int[0];
    private static final int NO_FREE_SLOTS = -1;
    final long stateFP; // fingerprint of the state
    final int tindex;
    /**
     * Next nodes are the successor {@link GraphNode}s of the current
     * {@link GraphNode}
     */
    private int[] nnodes; // outgoing links
    /**
     * Points to the first available slot in {@link GraphNode#nnodes} iff free
     * slots are available. "NO_FREE_SLOTS" indicates no free slots are available.
     *
     * @see GraphNode#allocate(int)
     */
    private int offset = NO_FREE_SLOTS;

    public GraphNode(final long fp, final int tindex) {
        this(fp, tindex, emptyIntArr, new BitSet(0));
    }

    private GraphNode(final long fp, final int tindex, final int[] nnodes, final BitSet checks) {
        super(checks);
        this.stateFP = fp;
        this.tindex = tindex;
        this.nnodes = nnodes;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + (int) (stateFP ^ (stateFP >>> 32));
        result = prime * result + tindex;
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
        final GraphNode other = (GraphNode) obj;
        if (stateFP != other.stateFP) {
            return false;
        }
        return tindex == other.tindex;
    }

    public final long getStateFP(final int i) {
        final long high = this.nnodes[NNODE_RECORD_SIZE * i];
        final long low = this.nnodes[NNODE_RECORD_SIZE * i + 1];
        return (high << 32) | (low & 0xFFFFFFFFL);
    }

    public final int getTidx(final int i) {
        return this.nnodes[NNODE_RECORD_SIZE * i + 2];
    }

    public final int succSize() {
        // offset being != NO_FREE_SLOTS indicates that the nnodes array has been
        // overallocated in preparation to batch-insert transitions but the
        // transitions have not been added yet. In this case the nnodes.length /
        // NNODE_RECORD_SIZE is *not* the actual number of transitions, offset / NNODE_RECORD_SIZE is!
        if (this.offset != NO_FREE_SLOTS) {
            return this.offset / NNODE_RECORD_SIZE;
        }
        return this.nnodes.length / NNODE_RECORD_SIZE;
    }

    /**
     * Allocates memory for subsequent
     * {@link GraphNode#addTransition(long, int, int, int, boolean[])} calls.
     * This is useful if
     * {@link GraphNode#addTransition(long, int, int, int, boolean[])} gets
     * invoked from within a loop when the approximate number of invocations is
     * known in advance. In this case {@link GraphNode} can reserve the memory
     * for the number of transitions in advance which greatly improves the
     * insertion time of
     * {@link GraphNode#addTransition(long, int, int, int, boolean[])}. Once all
     * transitions have been added to via
     * {@link GraphNode#addTransition(long, int, int, int, boolean[])},
     * optionally call the {@link GraphNode#realign()} method to discard of
     * unused memory.
     * <p>
     * Technically this essentially grows GraphNode's internal data structure.
     * <p>
     * Do note that you can call addTransition <em>without</em> calling allocate
     * first. It then automatically allocates a memory for a <em>single</em>
     * transition.
     *
     * @param transitions The approximate number of transitions that will be added
     *                    subsequently.
     * @see GraphNode#addTransition(long, int, int, int, boolean[])
     * @see GraphNode#realign()
     */
    private void allocate(final int transitions) {
        final int len = this.nnodes.length;
        final int[] newNodes = new int[len + (NNODE_RECORD_SIZE * transitions)];
        System.arraycopy(this.nnodes, 0, newNodes, 0, len);
        this.nnodes = newNodes;

        this.offset = len;
    }

    /**
     * Add a new transition to the node target.
     *
     * @param fp             fingerprint to add
     * @param tidx           tableau index to add
     * @param slen           number of solutions
     * @param alen           number of actions
     * @param acts           A {@link BitSet} of action results. Each bit in the vector
     *                       represents the result of the corresponding action (true or
     *                       false) returned by
     *                       tlc2.tool.liveness.OrderOfSolution.checkAction(TLCState,
     *                       TLCState, BitSet, int). <code>null</code> if no action
     *                       constraints to check.
     * @param actsOffset     The offset into the {@link BitSet} acts. acts may hold
     *                       action results for more than just the currently added
     *                       transition. In this case, provide an zero-based offset for
     *                       where the action results in BitSet start. 0 if the given
     *                       {@link BitSet} is exclusively used for the current
     *                       transition.
     * @param allocationHint A (Naturals \ {0}) hint telling the method's implementation
     *                       how many memory to allocate for subsequent transition
     *                       additions (used when called from within for loop). Zero or
     *                       negative hints are ignored (negative hints are the result of
     *                       nested for loop where the 1. iteration produces a bad average
     *                       of how many additions are made across all iterations).
     * @see GraphNode#allocate(int)
     */
    public final void addTransition(final long fp, final int tidx, final int slen, final int alen, final BitSet acts, final int actsOffset,
                                    final int allocationHint) {
        // Grows BitSet "checks" and sets the corresponding field to true if
        // acts is true (false is default and thus can be ignored).
        if (acts != null) {
            final int pos = slen + alen * this.succSize();
            for (int i = 0; i < alen; i++) {
                if (acts.get(actsOffset + i)) {
                    this.checks.set(pos + i);
                }
            }
        }
        if (this.offset == NO_FREE_SLOTS) {
            // Have to create a new slot regardless of 0 or negative hint, thus
            // Math.max...
            this.allocate(Math.max(allocationHint, 1));
        }
        this.nnodes[this.offset] = (int) (fp >>> 32);
        this.nnodes[this.offset + 1] = (int) (fp & 0xFFFFFFFFL);
        this.nnodes[this.offset + 2] = tidx;
        this.offset = this.offset + NNODE_RECORD_SIZE;
        if (this.offset == this.nnodes.length) {
            this.offset = NO_FREE_SLOTS;
        }
    }

    /**
     * Trims {@link GraphNode}'s internal data structure to its current real
     * memory requirement.
     *
     * @return The number of over allocated memory or zero if memory allocated
     * by corresponding allocate call has been used up completely.
     * @see GraphNode#allocate(int)
     */
    public int realign() {
        int result = 0;
        // It is a noop iff offset == NO_FREE_SLOTS
        if (this.offset != NO_FREE_SLOTS) {
            result = (this.nnodes.length - this.offset) / NNODE_RECORD_SIZE;
            // shrink newNodes to correct size
            final int[] newNodes = new int[this.offset];
            System.arraycopy(this.nnodes, 0, newNodes, 0, newNodes.length);
            this.nnodes = newNodes;
            this.offset = NO_FREE_SLOTS;
        }
        return result;
    }

    /* Return true iff there is an outgoing edge to target. */
    public final boolean transExists(final long fp, final int tidx) {
        // TODO Switch to a more efficient transExists implementation to handle
        // large numbers of transitions. The current implementation below uses a
        // linear search over all transitions.
        // The fact that the given fp is used as an index for hash-based lookup
        // methods in various places of TLC, makes it the obvious candidate as a
        // improved strategy. One behavioral difference a hash has, is that the
        // sequential iteration of all nnodes produces a different (yet stable)
        // order.
        int len = this.nnodes.length;
        // Stop linear search on internal nnodes buffer when a free slot has
        // been
        // reached. The free slot detection work with the allocation offset that
        // points to the end of the filled slots (slots are filled in ascending
        // order). If offset is marked invalid ("NO_FREE_SLOTS"), the nnodes buffer is
        // completely occupied and has to be searched to the end.
        if (this.offset != NO_FREE_SLOTS) {
            len = offset;
        }
        final int high = (int) (fp >>> 32);
        final int low = (int) (fp & 0xFFFFFFFFL);
        for (int i = 0; i < len; i += NNODE_RECORD_SIZE) {
            if (this.nnodes[i] == high && this.nnodes[i + 1] == low && this.nnodes[i + 2] == tidx) {
                return true;
            }
        }
        return false;
    }

    public boolean checkInvariants(final int slen, final int alen) {
        final Set<Transition> transitions = new HashSet<>();
        for (int i = 0; i < succSize(); i++) {
            final Transition t = new Transition(getStateFP(i), getTidx(i), getCheckAction(slen, alen, i));
            transitions.add(t);
        }
        return transitions.size() == succSize();
    }

    public Set<Transition> getTransition() {
        return getTransition(0, 0);
    }

    public Set<Transition> getTransition(final int slen, final int alen) {
        final Set<Transition> transitions = new HashSet<>();
        for (int i = 0; i < succSize(); i++) {
            final BitSet bv = new BitSet(alen);
            for (int j = 0; j < alen; j++) {
                if (getCheckAction(slen, alen, i, j)) {
                    bv.set(j);
                }
            }
            transitions.add(new Transition(getStateFP(i), getTidx(i), bv));
        }
        return transitions;
    }

    /* Return the tableau graph node used by this. */
    public final TBGraphNode getTNode(final TBGraph tableau) {
        return tableau.getNode(this.tindex);
    }

    /**
     * Writes this {@link GraphNode} into the given
     * {@link BufferedRandomAccessFile}
     */
    void write(final BufferedRandomAccessFile nodeRAF) throws IOException {
        assert offset == NO_FREE_SLOTS; // assert that nnodes hasn't been overallocated.
        // Write nnodes
        final int cnt = nnodes.length;
        nodeRAF.writeNat(cnt);
        for (final int nnode : nnodes) {
            nodeRAF.writeInt(nnode);
        }
        // Write checks
        BitSetUtilities.write(checks, nodeRAF);
    }

    void read(final BufferedRandomAccessFile nodeRAF) throws IOException {
        // Read nnodes
        final int cnt = nodeRAF.readNat();
        nnodes = new int[cnt];
        for (int i = 0; i < cnt; i++) {
            nnodes[i] = nodeRAF.readInt();
        }
        // Read checks
        checks = BitSetUtilities.fromFile(nodeRAF);

        assert offset == NO_FREE_SLOTS;
    }

    public final String toString() {
        // A GraphNode does not know the action length. This is kept elsewhere in the code.
        return toString(0).replace("[] ", "");
    }

    public final String toString(final int alen) {
        final StringBuilder buf = new StringBuilder();
        buf.append("<").append(this.stateFP).append(",").append(this.tindex).append("> --> ");
        for (int i = 0; i < succSize(); i++) {
            // action checks
            buf.append("[");
            for (int j = 0; j < alen; j++) {
                if (getCheckAction(0, 2, i, j)) {
                    buf.append("t");
                } else {
                    buf.append("f");
                }
            }
            buf.append("] ");
            // fingerprint/tableau id
            buf.append("<").append(getStateFP(i)).append(",").append(getTidx(i)).append(">");
            buf.append(", ");
        }
        return buf.substring(0, buf.length() - ", ".length()); // chop off dangling ", "
    }

    public String toDotViz(final boolean isInitState, final boolean hasTableau, final int slen, final int alen) {
        return toDotViz(isInitState, hasTableau, slen, alen, null);
    }

    public String toDotViz(final boolean isInitState, final boolean hasTableau, final int slen, final int alen, final TableauNodePtrTable filter) {
        // The node's id including its tidx if any. It uses the complete
        // fingerprint.
        String id = Long.toString(this.stateFP);
        if (hasTableau) {
            id += "." + this.tindex;
        }

        // Nodes label and a marker if it is an init state. The label is
        // shortened to 8 chars max to avoid screen clutter. It's possible
        // that the resulting graph will have multiple nodes with an identical
        // label iff the first 6 (+2) chars of their fingerprint match. However
        // the graph will still contain all nodes regardless of the label
        // collision due to id.
        final StringBuilder label = new StringBuilder(Long.toString(this.stateFP).substring(0, 6) + (hasTableau ? "." + this.tindex : ""));
        if (slen > 0) {
            label.append("\n");
            for (int i = 0; i < slen; i++) {
                if (getCheckState(i)) {
                    label.append("t");
                } else {
                    label.append("f");
                }
            }
        }
        final StringBuilder buf = new StringBuilder();
        if (isInitState) {
            buf.append("\"").append(id).append("\" [style = filled][label = \"").append(label).append("\"]\n"); // node's label
        } else {
            buf.append("\"").append(id).append("\" [label = \"").append(label).append("\"]\n");
        }

        // Each outgoing transition
        for (int i = 0; i < succSize(); i++) {
            final long stateFP = getStateFP(i);
            final int tidx = getTidx(i);

            // If a filter is given, check if this node is in filter
            if (filter != null && filter.get(stateFP, tidx) == -1) {
                continue;
            }

            final String fp = Long.toString(stateFP);

            buf.append("\"").append(id).append("\" -> ");
            if (hasTableau) {
                buf.append("\"").append(fp).append(".").append(tidx).append("\"");
            } else {
                //Omit tableau index when it's -1 (indicating no tableau)
                buf.append("\"").append(fp).append("\"");
            }

            buf.append(" [label=\"");
            for (int j = 0; j < alen; j++) {
                if (getCheckAction(slen, alen, i, j)) {
                    buf.append("t");
                } else {
                    buf.append("f");
                }
            }
            buf.append("\"];");
            buf.append("\n");
        }
        return buf.toString();
    }

    public static class Transition {

        private final long fp;
        private final int tidx;
        private final BitSet bv;

        public Transition(final long fp, final int tidx, final BitSet bv) {
            this.fp = fp;
            this.tidx = tidx;
            this.bv = bv;
        }

        /* (non-Javadoc)
         * @see java.lang.Object#hashCode()
         */
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + ((bv == null) ? 0 : bv.hashCode());
            result = prime * result + (int) (fp ^ (fp >>> 32));
            result = prime * result + tidx;
            return result;
        }

        /* (non-Javadoc)
         * @see java.lang.Object#equals(java.lang.Object)
         */
        public boolean equals(final Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            final Transition other = (Transition) obj;
            if (bv == null) {
                if (other.bv != null)
                    return false;
            } else if (!bv.equals(other.bv))
                return false;
            if (fp != other.fp)
                return false;
            return tidx == other.tidx;
        }

        public BitSet getChecks() {
            return bv;
        }

        public long getFP() {
            return fp;
        }

        public int getTidx() {
            return tidx;
        }
    }
}
