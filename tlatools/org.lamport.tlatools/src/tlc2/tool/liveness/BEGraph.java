// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:31 PST by lamport
//      modified on Wed Dec  5 22:41:28 PST 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.output.EC;
import tlc2.tool.EvalException;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.Objects;

public class BEGraph {
    /**
     * BEGraph represents the behaviour graph.
     */
    public final ArrayList<BEGraphNode> initNodes;
    public final String metadir;
    public final NodeTable allNodes;

    public BEGraph(final String metadir, final boolean isBT) {
        this.initNodes = new ArrayList<>();
        this.metadir = metadir;
        this.allNodes = new NodeTable(127, isBT);
    }

    /* Returns the shortest path from start to end (inclusive). */
    public static BEGraphNode[] getPath(final BEGraphNode start, final BEGraphNode end) {
        if (start.equals(end)) {
            start.setParent(null);
        } else {
            final boolean unseen = start.getVisited();
            final ArrayDeque<NodeAndParent> queue = new ArrayDeque<>(); // bomb if
            // checkpoint
            start.flipVisited();
            queue.add(new NodeAndParent(start, null));
            boolean found = false;
            while (!found) {
                final NodeAndParent np = queue.remove();
                if (np == null) {
                    throw new EvalException(EC.TLC_LIVE_BEGRAPH_FAILED_TO_CONSTRUCT);
                }
                final BEGraphNode curNode = np.node;
                for (int i = 0; i < curNode.nextSize(); i++) {
                    final BEGraphNode nextNode = curNode.nextAt(i);
                    if (nextNode.getVisited() == unseen) {
                        if (nextNode.equals(end)) {
                            end.setParent(curNode);
                            found = true;
                            break;
                        }
                        nextNode.flipVisited();
                        queue.add(new NodeAndParent(nextNode, curNode));
                    }
                }
                curNode.setParent(np.parent);
            }
        }
        // Get the path following parent pointers:
        final ArrayList<BEGraphNode> path = new ArrayList<>();
        BEGraphNode curNode = end;
        while (curNode != null) {
            path.add(curNode);
            curNode = curNode.getParent();
        }
        final int sz = path.size();
        final BEGraphNode[] bpath = new BEGraphNode[sz];
        for (int i = 0; i < sz; i++) {
            bpath[i] = path.get(sz - i - 1);
        }
        return bpath;
    }

    /**
     * This method resets the number field of all nodes in this behavior graph
     * to 0. Assume that all the nodes have non-zero number fields.
     */
    public final void resetNumberField() {
        final Deque<BEGraphNode> Deque = new ArrayDeque<>();
        for (final BEGraphNode node : this.initNodes) {
            if (node.resetNumberField() != 0) {
                Deque.push(node);
            }
        }
        while (!Deque.isEmpty()) {
            final BEGraphNode node = Deque.pop();
            for (int i = 0; i < Objects.requireNonNull(node).nextSize(); i++) {
                final BEGraphNode node1 = node.nextAt(i);
                if (node1.resetNumberField() != 0) {
                    Deque.push(node1);
                }
            }
        }
    }

    /* Returns the ith initial node. */
    public final BEGraphNode getInitNode(final int i) {
        return this.initNodes.get(i);
    }

    public final void addInitNode(final BEGraphNode node) {
        this.initNodes.add(node);
    }

    /* Returns the number of initial nodes. */
    public final int initSize() {
        return this.initNodes.size();
    }

    /**
     * This method assumes that the visited field of all the nodes is set to the
     * same value.
     */
    public final String toString() {
        final StringBuilder buf = new StringBuilder();
        final int sz = this.initNodes.size();
        if (sz != 0) {
            final boolean seen = this.getInitNode(0).getVisited();
            for (int i = 0; i < this.initNodes.size(); i++) {
                final BEGraphNode node = this.getInitNode(i);
                node.toString(buf, seen);
            }
        }
        return buf.toString();
    }

    private record NodeAndParent(BEGraphNode node, BEGraphNode parent) {
    }
}
