/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
package tlc2.tool.coverage;

import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;

import java.util.*;

public class OpApplNodeWrapper extends CostModelNode implements Comparable<OpApplNodeWrapper>, CostModel {

    protected final Map<SemanticNode, CostModelNode> lets = new LinkedHashMap<>();
    private final Set<Pair> childCounts = new HashSet<>();
    private final CostModelNode root;
    private final OpApplNode node;
    private final Set<Integer> seen = new HashSet<>();
    // Periodic coverage reporting executes concurrently with the evaluation of the
    // init and next-state relation. Traversing the CostModel trees to collect the
    // individual eval counts creates thus an inconsistent snapshot. To reduce the
    // inconsistency, freeze the eval count for all tree nodes on the first tree
    // traversal while the child counts are calculated. The snapshot is still
    // inconsistent from the perspective of the evaluation, but at least the
    // reporting in print (eval counts reported to parent - childCounts - and eval
    // counts printed is consistent. Alternatively, evaluation of init and next
    // could be suspended for the duration of the snapshot, but that seems overkill.
    private long snapshotEvalCount = 0;
    private long snapshotSecondCount = 0;
    private boolean primed = false;
    private int level;
    private CostModelNode recursive;

    OpApplNodeWrapper(final OpApplNode node, final CostModelNode root) {
        super();
        this.node = node;
        this.root = root;
        this.level = 0;
    }

    // For unit testing only.
    OpApplNodeWrapper() {
        this(null, null);
    }

    // ---------------- Identity... ---------------- //

    // For unit testing only.
    OpApplNodeWrapper(final OpApplNode node, final long samples) {
        this(node, null);
        this.incInvocations(samples);
    }

    protected static String indentBegin(final int n, final char c, final String str) {
        assert n >= 0;
        final String whitespaces = new String(new char[n]).replace('\0', c);
        return whitespaces + str;
    }

    @Override
    public int compareTo(final OpApplNodeWrapper arg0) {
        return this.getLocation().compareTo(arg0.getLocation());
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((node.getLocation() == null) ? 0 : node.getLocation().hashCode());
        return result;
    }

    // ----------------  ---------------- //

    @Override
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
        final OpApplNodeWrapper other = (OpApplNodeWrapper) obj;
        if (node.getLocation() == null) {
            return other.node.getLocation() == null;
        } else return node.getLocation().equals(other.node.getLocation());

    }

    @Override
    public String toString() {
        if (this.node == null) {
            return "root";
        }
        return node.toString();
    }

    @Override
    protected Location getLocation() {
        return this.node != null ? this.node.getLocation() : Location.nullLoc;
    }

    // ---------------- Parent <> Child ---------------- //

    @Override
    public OpApplNode getNode() {
        return this.node;
    }

    @Override
    public boolean isRoot() {
        return this.node == null;
    }

    public OpApplNodeWrapper addLets(final OpApplNodeWrapper lets) {
        this.lets.put(lets.getNode(), lets);
        return this;
    }

    public OpApplNodeWrapper setRecursive(final CostModelNode recursive) {
        assert this.recursive == null;
        this.recursive = recursive;
        return this;
    }

    @Override
    public CostModelNode getRoot() {
        assert this.root instanceof ActionWrapper;
        return this.root;
    }

    // ---------------- Level ---------------- //

    @Override
    public final CostModelNode get(final SemanticNode eon) {
        if (eon == this.node || !(eon instanceof OpApplNode)) {
            return this;
        }

        CostModelNode child = children.get(eon);
        if (child != null) {
            return child;
        }

        if (recursive != null) {
            child = recursive.children.get(eon);
            if (child != null) {
                return child;
            }
        }

        child = lets.get(eon);
        if (child != null) {
            return child;
        }

        // TODO Not all places in Tool lookup the correct CM yet. This should only be an
        // engineering effort though.
        if (seen.add(eon.myUID)) {
            //...only report it once to not spam the Toolbox console.
            MP.printMessage(EC.TLC_COVERAGE_MISMATCH, eon.toString(), this.toString());
        }
        return this;
    }

    @Override
    public int getLevel() {
        return this.level;
    }

    // ---------------- Primed ---------------- //

    public OpApplNodeWrapper setLevel(final int level) {
        this.level = level;
        return this;
    }

    public OpApplNodeWrapper setPrimed() {
        assert !isPrimed();
        this.primed = true;
        return this;
    }

    // ---------------- Print ---------------- //

    protected boolean isPrimed() {
        return this.primed;
    }

    protected long getEvalCount(final Calculate fresh) {
        if (fresh == Calculate.FRESH) {
            return super.getEvalCount();
        } else {
            return snapshotEvalCount;
        }
    }

    protected long getSecondCount(final Calculate fresh) {
        if (fresh == Calculate.FRESH) {
            return super.getSecondary();
        } else {
            return snapshotSecondCount;
        }
    }

    @Override
    public CostModel report() {
        print(0, Calculate.FRESH);
        return this;
    }

    protected void print(int level, final Calculate fresh) {
        final Set<Pair> collectedEvalCounts = new HashSet<>();
        this.collectChildren(collectedEvalCounts, fresh);
        if (collectedEvalCounts.isEmpty()) {
            // Subtree has nothing to report.
            if (getEvalCount(fresh) == 0L && !isPrimed()) {
                // ..this node neither (eval count zero => secondary zero).
                return;
            } else {
                printSelf(level++);
                return; // Do not invoke printSelf(...) again below.
            }
        }
        final Pair node = new Pair(getEvalCount(fresh), getSecondCount(fresh));

        if (collectedEvalCounts.size() == 1) {
            // The eval and secondary count of all children is consistent. We can, thus,
            // collapse subtrees into this node under the following cases.
            final Pair consistentChildren = getCount(collectedEvalCounts);

            if (Objects.requireNonNull(consistentChildren).primary < node.primary) {
                // Cannot collapse subtree because inconsistent with this node.
                printSelf(level++);
                printChildren(level);
                return;
            }
            if (!isPrimed() && node.isZero() && consistentChildren.isNonZero()) {
                // Collapse consistent subtree into this node unless this node is primed.
                if (consistentChildren.secondary == 0L) {
                    printSelf(level++, consistentChildren.primary);
                } else {
                    printSelf(level++, consistentChildren.primary, consistentChildren.secondary);
                }
                return;
            }
            if (node.isZero() && consistentChildren.isZero()) {
                if (isPrimed()) {
                    printSelf(level++);
                }
                // Have a primed in subtree.
                printChildren(level);
                return;
            }
            if (node.equals(consistentChildren)) {
                // Have a primed in subtree.
                printSelf(level++);
                return;
            }
        }

        // Subtree is inconsistent and needs to report itself.
        if (node.isNonZero() || isPrimed()) {
            printSelf(level++);
        }
        printChildren(level);
    }

    private Pair getCount(final Set<Pair> collectWeights) {
        assert collectWeights.size() == 1;
        for (final Pair l : collectWeights) {
            return l;
        }
        return null; // make compiler happy
    }

    protected void printChildren(final int level) {
        for (final CostModelNode cmn : children.values()) {
            ((OpApplNodeWrapper) cmn).print(level, Calculate.CACHED);
        }
    }

    protected void printSelf(final int level, final long count) {
        MP.printMessage(EC.TLC_COVERAGE_VALUE, indentBegin(level, TLCGlobals.coverageIndent, getLocation().toString()), String.valueOf(count));
    }

    protected void printSelf(final int level, final long count, final long cost) {
        MP.printMessage(EC.TLC_COVERAGE_VALUE_COST,
                indentBegin(level, TLCGlobals.coverageIndent, getLocation().toString()),
                String.valueOf(count), String.valueOf(cost));
    }

    protected void printSelf(final int level) {
        if (getSecondary() > 0) {
            printSelf(level, getEvalCount(), getSecondary());
        } else {
            printSelf(level, getEvalCount());
        }
    }

    protected void collectChildren(final Set<Pair> result, final Calculate c) {
        for (final CostModelNode cmn : children.values()) {
            ((OpApplNodeWrapper) cmn).collectAndFreezeEvalCounts(result, c);
        }
    }

    // ---------------- Child counts ---------------- //

    protected void collectAndFreezeEvalCounts(final Set<Pair> result, final Calculate c) {
        if (c == Calculate.FRESH) {
            snapshotEvalCount = this.getEvalCount(c);
            snapshotSecondCount = this.getSecondCount(c);
            childCounts.clear();
            if (snapshotEvalCount > 0 || snapshotSecondCount > 0 || this.isPrimed()) {
                childCounts.add(new Pair(snapshotEvalCount, snapshotSecondCount));
            }
            collectChildren(childCounts, c);
        }
        result.addAll(childCounts);
    }

    protected enum Calculate {
        FRESH, CACHED
    }

    static class Pair {
        public final long primary;
        public final long secondary;

        public Pair(final long primary, final long secondary) {
            this.primary = primary;
            this.secondary = secondary;
        }

        public boolean isZero() {
            return primary == 0 && secondary == 0;
        }

        public boolean isNonZero() {
            return primary > 0 || secondary > 0;
        }

        @Override
        public int hashCode() {
            return Objects.hash(primary, secondary);
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            final Pair other = (Pair) obj;
            return primary == other.primary && secondary == other.secondary;
        }

        @Override
        public String toString() {
            return "<<" + primary + ", " + secondary + ">>";
        }
    }
}