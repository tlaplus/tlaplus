/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package tlc2.tool.liveness;

/**
 * {@link TableauNodePtrTable} (and its sibling {@link NodePtrTable} for
 * tableau-less liveness checking) is a - highly optimized - set of all nodes in
 * the behavior graph {@link TableauDiskGraph}.
 * <p>
 * Each node in the behavior graph consists of the pair <<state, tidx>> (where
 * state is a state's fingerprint) and auxiliary information. The auxiliary
 * information is:
 * <ul>
 * <li>An offset into the second set (@see {@link AbstractDiskGraph#nodeRAF})
 * which represents the arcs between the nodes (logically outgoing transitions).
 * Technically this is a pointer location into the second disk file of
 * {@link TableauDiskGraph}.</li>
 * <li>The node's link number during Tarjan's SCC search.</li>
 * <li>A flag if the node is done or not (see {@link TableauNodePtrTable#UNDONE}
 * below).</li>
 * <li>A flag that marks a node an initial node.</li>
 * <li>A flag if the node has been seen before during error trace re-creation
 * (see {@link LiveWorker#printTrace}.</li>
 * </ul>
 * <p>
 * The last item indicates that this class is used in two scenarios. It's
 * primary purpose is to be the backing store of the liveness/behavior disc
 * graph. Additionally though, LiveWorker#printTrace independently instantiates
 * a new {@link TableauNodePtrTable} to do its work.
 * <p>
 * To minimize {@link TableauNodePtrTable}'s space/memory requirements, the
 * auxiliary information replace each other depending on the phase of liveness
 * checking.<br>
 * During model checking (safety checking) the auxiliary information is set to a
 * pointer location (long) pointing into the arcs set and the high bits of the
 * long are used to mark nodes as done or undone.<br>
 * As soon as the SCC search starts, the pointer location is replaced by the SCC
 * link number.<br>
 * Once a liveness violation has been detected, the seen flag is set during the
 * error trace path reconstruction.
 * <p>
 * Internally {@link TableauNodePtrTable} hashes the node's fingerprint to a
 * bucket address. In case of hash collision, open addressing is used.
 */
public class TableauNodePtrTable {

    /**
     * A node is marked UNDONE if it is:
     * <ul>
     * <li>An initial node <b>s0</b> and not yet visited again by
     * LiveChecker#addNextState(<b>s0</b>)</li>
     * <li>A previously unseen successor node <b>t</b> of a node <b>s</b> that
     * is added as an outgoing transition of <b>s</b> when <b>s</b> is being
     * added via LiveChecker#addNextState(<b>s</b> )</li>
     * </ul>
     * <p>
     * It logically markers the successor node <b>t</b> to be incomplete which
     * can only happen during liveness checking of a <b>partial</b> liveness
     * graph.
     */
    public static final long UNDONE = 0xFFFFFFFE00000000L;
    /*
     * Helper methods used by LiveWorker#printTrace(..) only. Note that
     * printTrace does not use the TNPT instance of the DiskGraph but its own
     * instance only containing a single SCC.
     */
    public static final int END_MARKER = -1;
    public static final int NO_PARENT = -1;
    private int count;
    private int length;
    private int thresh;
    private int[][] nodes;

    public TableauNodePtrTable(final int size) {
        this.count = 0;
        this.length = size;
        this.thresh = (int) (size * 0.75);
        this.nodes = new int[size][];
    }

    private static int[] addKey(final long key) {
        final int[] node = new int[2];
        node[0] = (int) (key >>> 32);
        node[1] = (int) (key & 0xFFFFFFFFL);
        return node;
    }

    public static long getKey(final int[] node) {
        final long high = node[0];
        final long low = node[1];
        return (high << 32) | (low & 0xFFFFFFFFL);
    }

    public static long getElem(final int[] node, final int loc) {
        final long high = node[loc + 1];
        final long low = node[loc + 2];
        return (high << 32) | (low & 0xFFFFFFFFL);
    }

    public static void putElem(final int[] node, final long elem, final int loc) {
        node[loc + 1] = (int) (elem >>> 32);
        node[loc + 2] = (int) (elem & 0xFFFFFFFFL);
    }

    public static int getTidx(final int[] node, final int loc) {
        return node[loc];
    }

    public static int startLoc(final int[] node) {
        return (node.length > 2) ? 2 : END_MARKER;
    }

    public static int nextLoc(final int[] node, final int curLoc) {
        final int loc = curLoc + 3;
        return (loc < node.length) ? loc : END_MARKER;
    }

    /**
     * @return True, iff the record at tloc has been marked seen.
     * @see TableauNodePtrTable#setSeen(int[], int)
     */
    public static boolean isSeen(final int[] nodes, final int tloc) {
        return getElem(nodes, tloc) < 0;
    }

    /**
     * Marks the record at tloc seen.
     *
     * @see TableauNodePtrTable#setSeen(int[])
     * @see TableauNodePtrTable#resetElems()
     */
    public static void setSeen(final int[] nodes, final int tloc) {
        final long ptr = getElem(nodes, tloc);
        putElem(nodes, (ptr | 0x8000000000000000L), tloc); // Set the MSB
    }

    public static long getPtr(final long ptr) {
        return (ptr & 0x7FFFFFFFFFFFFFFFL);
    }

    /**
     * @return True, iff the record has been marked seen.
     * @see TableauNodePtrTable#setSeen(int[])
     */
    public static boolean isSeen(final int[] nodes) {
        return nodes[3] < 0;
    }

    /**
     * Marks this record seen.
     *
     * @see TableauNodePtrTable#resetElems()
     */
    public static void setSeen(final int[] nodes) {
        nodes[3] |= 0x80000000; // Set the MSB
    }

    /*
     * Private static helper methods below
     */

    public static int getParent(final int[] nodes) {
        return nodes[4];
    }

    public static void setParent(final int[] nodes, final int loc) {
        assert loc >= NO_PARENT && loc <= AbstractDiskGraph.MAX_PTR;
        nodes[4] = loc;
    }

    /* The number of elements in this table. */
    public final int size() {
        return this.count;
    }

    /*
     * Static helper methods below
     */

    public final int getSize() {
        return this.length;
    }

    /**
     * Return the value associated with the key <k, tidx> if the table contains
     * <k, tidx>. Otherwise, return -1.
     */
    public final long get(final long k, final int tidx) {
        if (count >= thresh) {
            this.grow();
        }
        int loc = ((int) k & 0x7FFFFFFF) % this.length;
        while (true) {
            final int[] node = this.nodes[loc];
            if (node == null) {
                return -1;
            }
            if (getKey(node) == k) {
                final int idx = getIdx(node, tidx);
                if (idx == -1) {
                    return -1;
                }
                return getElem(node, idx);
            }
            loc = (loc + 1) % this.length;
        }
    }

    /**
     * Add <tidx, elem> into the table. If the table has already contained <k,
     * tidx>, overwrite the old value.
     */
    public final void put(final long k, final int tidx, final long elem) {
        if (this.count >= this.thresh) {
            this.grow();
        }
        int loc = ((int) k & 0x7FFFFFFF) % this.length;
        while (true) {
            final int[] node = this.nodes[loc];
            if (node == null) {
                this.nodes[loc] = addElem(k, tidx, elem);
                this.count++;
                return;
            }
            // Verify that the node at position loc has the correct key. Due to
            // hash collisions, it might be a different node that hashes to the
            // same bucket. If this is the case, increment the location to check
            // the next bucket (loc + 1 below).
            if (getKey(node) == k) {
                // Iff this is the correct key, search through the nodes and get
                // the one with the matching tableau index.
                final int cloc = getIdx(node, tidx);
                if (cloc == -1) {
                    // The list of nodes does not contain the give tableau idx
                    // yet, thus append a new element. Technically, it means we
                    // grow the nodes array by three and insert the tableau idx
                    // and its element.
                    this.nodes[loc] = appendElem(node, tidx, elem);
                } else {
                    // Nodes already contains an entry for the given tableau.
                    // Update its element. The element is either a pointer
                    // location, MAX_LINK, MAX_PTR or a REACHABLE mark. The
                    // previous value is overwritten.
                    putElem(this.nodes[loc], elem, cloc);
                }
                return;
            }
            loc = (loc + 1) % this.length;
        }
    }

    /**
     * Return k's location if the table contains <k, tidx>. Otherwise, return
     * -1.
     */
    public final int getLoc(final long k, final int tidx) {
        if (count >= thresh) {
            this.grow();
        }
        int loc = ((int) k & 0x7FFFFFFF) % this.length;
        while (true) {
            final int[] node = this.nodes[loc];
            if (node == null) {
                return -1;
            }
            if (getKey(node) == k) {
                if (getIdx(node, tidx) == -1) {
                    return -1;
                }
                return loc;
            }
            loc = (loc + 1) % this.length;
        }
    }

    /* Return all nodes with key k. Return null if this does not contain k. */
    public final int[] getNodes(final long k) {
        if (count >= thresh) {
            this.grow();
        }
        int loc = ((int) k & 0x7FFFFFFF) % this.length;
        while (true) {
            final int[] node = this.nodes[loc];
            if (node == null) {
                return null;
            }
            if (getKey(node) == k) {
                return this.nodes[loc];
            }
            loc = (loc + 1) % this.length;
        }
    }

    /* Return k's location. Return -1 if this does not contain k. */
    public final int getNodesLoc(final long k) {
        if (count >= thresh) {
            this.grow();
        }
        int loc = ((int) k & 0x7FFFFFFF) % this.length;
        while (true) {
            final int[] node = this.nodes[loc];
            if (node == null) {
                return -1;
            }
            if (getKey(node) == k) {
                return loc;
            }
            loc = (loc + 1) % this.length;
        }
    }

    public final int[] getNodesByLoc(final int loc) {
        return this.nodes[loc];
    }

    /**
     * This method returns true iff we have already done the nodes with key k.
     * If we have done with k and a new node is being added, we must get this
     * new node done.
     */
    public final boolean isDone(final long k) {
        final int[] node = this.getNodes(k);
        if (node == null) {
            return false;
        }
        if (node.length == 2) {
            return true;
        }
        // see NOT_DONE constant".
        return node[3] != -2;
    }

    // Called by addNextState
    public final int setDone(final long k) {
        if (this.count >= this.thresh) {
            this.grow();
        }
        int loc = ((int) k & 0x7FFFFFFF) % this.length;
        while (true) {
            final int[] node = this.nodes[loc];
            if (node == null) {
                this.nodes[loc] = addKey(k);
                this.count++;
                return loc;
            }
            if (getKey(node) == k) {
                if (node.length > 2 && node[3] == -2) {
                    // Set this to something other than -2 (see NOT_DONE).
                    node[3] = -3;
                }
                return loc;
            }
            loc = (loc + 1) % this.length;
        }
    }

    private void put(final int[] node) {
        final long k = getKey(node);
        int loc = ((int) k & 0x7FFFFFFF) % this.length;
        while (true) {
            if (this.nodes[loc] == null) {
                this.nodes[loc] = node;
                return;
            }
            loc = (loc + 1) % this.length;
        }
    }

    /**
     * Clears the seen flag of all records set by static setSeen(..) calls
     * earlier.
     * <p>
     * Post-Condition: None of the records is marked seen.
     *
     * @see TableauNodePtrTable#setSeen(int[])
     * @see TableauNodePtrTable#setSeen(int[], int)
     */
    public final void resetElems() {
        // Only called when the error trace is being printed.
        for (final int[] node : this.nodes) {
            if (node != null) {
                for (int j = 3; j < node.length; j += getElemLength()) {
                    node[j] &= 0x7FFFFFFF; // Clear the MSB set by setSeen(..)
                }
            }
        }
    }

    /* Double the table when the table is full by the threshhold. */
    private void grow() {
        this.length = 2 * this.length + 1;
        this.thresh = (int) (this.length * 0.75);
        final int[][] oldNodes = this.nodes;
        this.nodes = new int[this.length][];
        for (final int[] node : oldNodes) {
            if (node != null) {
                this.put(node);
            }
        }
    }

    /**
     * @return The length of an elem "record" in nodes[]
     */
    public int getElemLength() {
        return 3;
    }

    protected int[] addElem(final long key, final int tidx, final long elem) {
        final int[] node = new int[3 + getElemLength() - 1];
        node[0] = (int) (key >>> 32);
        node[1] = (int) (key & 0xFFFFFFFFL);
        node[2] = tidx;
        node[3] = (int) (elem >>> 32);
        node[4] = (int) (elem & 0xFFFFFFFFL);
        return node;
    }

    protected int[] appendElem(final int[] node, final int tidx, final long elem) {
        final int len = node.length;
        final int[] newNode = new int[len + getElemLength()];
        System.arraycopy(node, 0, newNode, 0, len);
        newNode[len] = tidx;
        newNode[len + 1] = (int) (elem >>> 32);
        newNode[len + 2] = (int) (elem & 0xFFFFFFFFL);
        return newNode;
    }

    public final int getIdx(final int[] node, final int tidx) {
        final int len = node.length;
        for (int i = 2; i < len; i += getElemLength()) {
            if (node[i] == tidx) {
                return i;
            }
        }
        return -1;
    }

    public int getElemTidx(final int[] node, final int loc) {
        // This implementation does not store the tableau index.
        return -1;
    }

    public void putElem(final int[] node, final long elem, final int tableauIdx, final int loc) {
        node[loc + 1] = (int) (elem >>> 32);
        node[loc + 2] = (int) (elem & 0xFFFFFFFFL);
        // ignores tableau index
    }

    /*
     * The detailed formatter below can be activated in Eclipse's variable view
     * by choosing "New detailed formatter" from the nodePtrTable's context menu.
     * Insert "TableauNodePtrTable.DetailedFormatter.toString(this);".
     */
    public static class DetailedFormatter {
        public static String toString(final TableauNodePtrTable table) {
            final StringBuilder buf = new StringBuilder(table.count);
            for (int i = 0; i < table.nodes.length; i++) {
                if (table.nodes[i] != null) {
                    final int[] node = table.nodes[i];

                    // fingerprint
                    final long fp = ((long) node[0] << 32) | (node[1] & 0xFFFFFFFFL);
                    buf.append("fp (key): ").append(fp);
                    buf.append(" (idx: ").append(i).append(")");
                    buf.append(" isDone: ").append(node.length == 2 || (node.length > 2 && node[3] != -2));
                    buf.append("\n");

                    // A node maintains n records. Each record logically
                    // contains information - combined with the fingerprint -
                    // about the full tuple <<fp, tidx, loc>>.
                    // Depending on the state of the record, the loc might
                    // also be overwritten by the SCC link number.
                    int j = 2;
                    for (; j < node.length - 1; j += table.getElemLength()) { // don't miss the ptr at the end
                        buf.append("\t");
                        // tableau index
                        final int tidx = node[j];
                        buf.append(" tidx: ").append(tidx);
                        // element
                        final long elem = getElem(node, j);
                        if (AbstractDiskGraph.isFilePointer(elem)) {
                            if (table.isDone(fp)) {
                                buf.append("  ptr: ").append(elem);
                            } else {
                                buf.append("  ptr: undone");
                            }
                        } else if (AbstractDiskGraph.MAX_PTR == elem) {
                            buf.append(" elem: Init State");
                        } else {
                            final long offset = AbstractDiskGraph.MAX_PTR + 1;
                            buf.append(" pred: ").append(elem - offset);
                        }
                        final int predTidx = table.getElemTidx(node, j);
                        if (predTidx != -1) {
                            buf.append(" predtidx: ").append(predTidx);
                        }
                        buf.append(", isSeen: ").append(isSeen(node, j));
                        buf.append("\n");
                    }
                }
            }
            return buf.toString();
        }
    }
}
