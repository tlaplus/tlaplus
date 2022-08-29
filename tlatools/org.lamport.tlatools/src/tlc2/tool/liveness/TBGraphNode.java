// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:50 PST by lamport
//      modified on Sun Aug  5 00:16:15 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tla2sany.semantic.LevelConstants;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.util.SetOfLong;

import java.util.ArrayList;

public class TBGraphNode {
    public final ArrayList<TBGraphNode> nexts; // outlinks
    /**
     * TBGraphNode represents a node in the tableau graph. Read MP for what a
     * particle tableau graph is. We give each node in the tableau-graph an
     * index because it might be useful for hashing. statePreds are deduced from
     * the particle at the moment of creation. They are later used in checking
     * if a state-node is consistent with a tableau-node.
     */
    private final TBPar par; // particle
    private final LiveExprNode[] statePreds; // state predicates in the particle
    private int index; // unique id for this node


    public TBGraphNode(final TBPar par) {
        this.par = par;
        this.index = 0;
        this.nexts = new ArrayList<>();
        final TBPar preds = new TBPar(par.size());
        for (int i = 0; i < par.size(); i++) {
            final LiveExprNode ln = par.exprAt(i);
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
                preds.add(ln);
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

    public TBGraphNode nextAt(final int i) {
        return this.nexts.get(i);
    }


    /**
     * Checks if this particle node is consistent with the given
     * {@link TLCState}. In other words, it checks if {@link TLCState}'s truth
     * values according to all state predicates of the tableau node. The state
     * predicates are deduced from the particles during tableau construction.
     */
    public boolean isConsistent(final TLCState state, final ITool tool) {
        for (final LiveExprNode statePred : this.statePreds) {
            if (!statePred.eval(tool, state, null)) {
                return false;
            }
        }
        return true;
    }

    private boolean isSelfLoop() {
        if (nextSize() == 1) {
            return nextAt(0) == this;
        }
        return false;
    }

    public final boolean isAccepting() {
        return par.isEmpty() && isSelfLoop();
    }

    public final String toString() {
        final StringBuilder buf = new StringBuilder();
        final SetOfLong visited = new SetOfLong(16);
        this.toString(buf, visited);
        return buf.toString();
    }

    private void toString(final StringBuilder buf, final SetOfLong visited) {
        if (!visited.put(this.index)) {
            buf.append(this.par.toString());
            for (int i = 0; i < this.nexts.size(); i++) {
                buf.append(this.nextAt(i).index).append(" ");
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

        final StringBuilder buf = new StringBuilder(nextSize());
        buf.append(this.index).append(" [label=").append(label).append("]\n"); // nodes label
        if (isInitNode) {
            buf.append("[style = filled]\n");
        }
        for (int i = 0; i < nextSize(); i++) {
            final TBGraphNode successor = nextAt(i);
            buf.append(this.index).append(" -> ").append(successor.index);
            buf.append("\n");
        }
        return buf.toString();
    }
}

