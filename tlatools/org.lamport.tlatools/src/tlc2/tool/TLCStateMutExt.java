// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:01 PST by lamport
//      modified on Wed Dec  5 23:18:37 PST 2001 by yuanyu

package tlc2.tool;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.TLCGlobals;
import tlc2.util.Context;
import tlc2.util.FP64;
import tlc2.value.*;
import util.UniqueString;
import util.WrongInvocationException;

import java.io.IOException;
import java.io.Serializable;
import java.util.Comparator;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.Callable;

/**
 * Attention! Copy of TLCStateMut except for getter/setter and fields callable,
 * predecessor and action.
 */
public final class TLCStateMutExt extends TLCState implements Cloneable, Serializable {
    private static final long serialVersionUID = 26539988826590236L;
    private final IValue[] values;
    private final ITool mytool;

    /**
     * If non-null, viewMap denotes the function to be applied to
     * a state before its fingerprint is computed.
     */
    private final SemanticNode viewMap;

    /**
     * If non-null, perms denotes the set of permutations under the
     * symmetry assumption.
     */
    private final IMVPerm[] perms;
    private Action action;
    private TLCState predecessor;
    private Callable<?> callable;

    private TLCStateMutExt(final OpDeclNode[] vars, final IValue[] vals, final ITool tool) {
        this(vars, vals, tool, tool.getViewSpec(), tool.getSymmetryPerms());
    }

    private TLCStateMutExt(final OpDeclNode[] vars, final IValue[] vals, final ITool tool, final SemanticNode viewMap, final IMVPerm[] perms) {
        super(vars);
        this.values = vals;
        this.mytool = tool;
        this.viewMap = viewMap;
        this.perms = perms;
    }

    private TLCStateMutExt(final short workerId, final long uid, final int level, final OpDeclNode[] vars, final IValue[] vals, final ITool tool, final SemanticNode viewMap, final IMVPerm[] perms) {
        super(workerId, uid, level, vars);
        this.values = vals;
        this.mytool = tool;
        this.viewMap = viewMap;
        this.perms = perms;
    }

    public static TLCState getEmpty(final OpDeclNode[] vars, final ITool tool) {
        final IValue[] vals = new IValue[vars.length];
        return new TLCStateMutExt(vars, vals, tool);
        // SZ 10.04.2009: since this method is called exactly one from Spec#processSpec
        // moved the call of UniqueString#setVariables to that place
    }

    @Override
    public TLCState createEmpty() {
        final IValue[] vals = new IValue[vars.length];
        return new TLCStateMutExt(vars, vals, mytool, viewMap, perms);
    }

    @Override
    public TLCState createNewFromValueStream(final IValueInputStream vis) throws IOException {
        var workerId = vis.readShortNat();
        var uid = vis.readLongNat();
        var level = vis.readShortNat();

        final IValue[] vals = new IValue[vars.length];
        final int len = vals.length;
        for (int i = 0; i < len; i++) {
            vals[i] = vis.read();
        }

        return new TLCStateMutExt(workerId, uid, level, vars, vals, mytool, viewMap, perms);
    }

    //TODO equals without hashcode!
    public boolean equals(final Object obj) {
        if (obj instanceof final TLCStateMutExt state) {
            for (int i = 0; i < this.values.length; i++) {
                if (this.values[i] == null) {
                    if (state.values[i] != null) return false;
                } else if (state.values[i] == null ||
                        !this.values[i].equals(state.values[i])) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    @Override
    public TLCState bind(final UniqueString name, final IValue value) {
        // Note, tla2sany.semantic.OpApplNode.toString(Value) relies on this ordering.
        final int loc = name.getVarLoc(values.length);
        this.values[loc] = value;
        return this;
    }

    @Override
    public TLCState bind(final SymbolNode id, final IValue value) {
        throw new WrongInvocationException("TLCStateMut.bind: This is a TLC bug.");
    }

    @Override
    public TLCState unbind(final UniqueString name) {
        final int loc = name.getVarLoc(values.length);
        this.values[loc] = null;
        return this;
    }

    @Override
    public IValue lookup(final UniqueString var) {
        final int loc = var.getVarLoc(values.length);
        if (loc < 0) return null;
        return this.values[loc];
    }

    @Override
    public boolean containsKey(final UniqueString var) {
        return (this.lookup(var) != null);
    }

    @Override
    public TLCState copy() {
        final int len = this.values.length;
        final IValue[] vals = new IValue[len];
        System.arraycopy(this.values, 0, vals, 0, len);
        return copyExt(new TLCStateMutExt(vars, vals, mytool, viewMap, perms));
    }

    @Override
    public TLCState deepCopy() {
        final int len = this.values.length;
        final IValue[] vals = new IValue[len];
        for (int i = 0; i < len; i++) {
            final IValue val = this.values[i];
            if (val != null) {
                vals[i] = val.deepCopy();
            }
        }
        return deepCopy(new TLCStateMutExt(vars, vals, mytool, viewMap, perms));
    }

    @Override
    public StateVec addToVec(final StateVec states) {
        return states.addState(this.copy());
    }

    @Override
    public void deepNormalize() {
        for (final IValue val : this.values) {
            if (val != null) {
                val.deepNormalize();
            }
        }
    }

    public long generateFingerPrint() {
        final int sz = this.values.length;

        // TLC supports symmetry reduction. Symmetry reduction works by defining classes
        // of symmetrically equivalent states for which TLC only checks a
        // single representative of the equivalence class (orbit). E.g. in a two
        // process mutual exclusion problem, the process ids are - most of the time -
        // not relevant with regards to mutual exclusion: We don't care if process A or
        // B is in the critical section as long as only a single process is in CS. Thus
        // two states are symmetric that only differ in the process id variable value.
        // Symmetry can also be observed graphically in the state graph s.t. subgraphs
        // are isomorphic (Graph Isomorphism). Instead of enumerating the complete state
        // graph, TLC enumerates one of the isomorphic subgraphs whose state correspond
        // to the representatives. With respect to the corresponding Kripke structure M,
        // the resulting Kripke M' is called the "quotient structure" (see "Exploiting
        // Symmetry in Temporal Logic Model Checking" by Clarke et al).
        //
        // The definition of equivalence classes (orbits) is provided manually by the
        // user at startup by defining 1 to n symmetry sets. Thus TLC has to find
        // representative at runtime only which happens below. Given any state s, TLC
        // evaluates rep(s) to find the lexicographically smallest state ss = rep(s)
        // with regards to the variable values. The state ss is then fingerprint instead
        // of s.
        //
        // Evaluating rep(s) - to reduce s to ss - requires to apply all permutations in
        // the group this.perms (derived from the user-defined orbit). This is known as
        // the constructive orbit problem and is NP-hard. The loop has O(|perms| * |this.values|)
        // with |prems| = |symmetry set 1|! * |symmetry set 2|! * ... * |symmetry set n|.
        //
        // minVals is what is used to calculate/generate the fingerprint below.
        // If this state is not the lexicographically smallest state ss, its current
        // minVals will be replaced temporarily with the values of ss for the
        // calculation of the fingerprint.
        IValue[] minVals = this.values;
        if (perms != null) {
            IValue[] vals = new IValue[sz];
            // The following for loop converges to the smallest state ss under symmetry by
            // looping over all permutations applying each. If the outcome turns out to be
            // lexicographically smaller than the currently smallest, it replaces the
            // current smallest. Once all permutations (perms) have been processed, we know
            // we have found the smallest state.
            NEXT_PERM:
            for (final IMVPerm perm : perms) {
                int cmp = 0;
                // For each value in values succinctly permute the current value
                // and compare it to its corresponding minValue in minVals.
                for (int j = 0; j < sz; j++) {
                    vals[j] = this.values[j].permute(perm);
                    if (cmp == 0) {
                        // Only compare unless an earlier compare has found a
                        // difference already (if a difference has been found
                        // earlier, still permute the remaining values of the
                        // state to fully permute all state values).
                        cmp = vals[j].compareTo(minVals[j]);
                        if (cmp > 0) {
                            // When cmp evaluates to >0, all subsequent
                            // applications of perms[i] for the remaining values
                            // won't make the resulting vals[] smaller than
                            // minVals. Thus, exit preemptively from the loop
                            // over vals. This works because perms is the cross
                            // product of all symmetry sets.
                            continue NEXT_PERM;
                        }
                    }
                }
                // cmp < 0 means the current state is part of a symmetry
                // permutation set/group and not the "smallest" one.
                if (cmp < 0) {
                    if (minVals == this.values) {
                        minVals = vals;
                        vals = new IValue[sz];
                    } else {
                        final IValue[] temp = minVals;
                        minVals = vals;
                        vals = temp;
                    }
                }
            }
        }
        // Fingerprint the state:
        long fp = FP64.New();
        if (viewMap == null) {
            for (int i = 0; i < sz; i++) {
                fp = minVals[i].fingerPrint(fp);
            }
            if (this.values != minVals) {
                for (final IValue value : this.values) {
                    value.deepNormalize();
                }
            }
        } else {
            for (final IValue value : this.values) {
                value.deepNormalize();
            }
            TLCStateMutExt state = this;
            if (minVals != this.values) {
                state = new TLCStateMutExt(vars, minVals, mytool, viewMap, perms);
            }
            final IValue val = mytool.eval(viewMap, Context.Empty, state);
            fp = val.fingerPrint(fp);
        }
        return fp;
    }

    /**
     * This method returns the fingerprint of this state. We fingerprint
     * the values in the state according to the order given by vars.
     * This guarantees the same state has the same fingerprint.
     * <p>
     * Since the values in this state can be shared by multiple threads
     * via the state queue. They have to be normalized before adding to
     * the state queue.  We do that here.
     */
    @Override
    public long fingerPrint() {
        return generateFingerPrint();
    }

    @Override
    public boolean allAssigned() {
        for (final IValue value : this.values) {
            if (value == null) return false;
        }
        return true;
    }

    @Override
    public boolean noneAssigned() {
        for (final IValue value : this.values) {
            if (value != null) {
                return false;
            }
        }
        return true;
    }

    @Override
    public Set<OpDeclNode> getUnassigned() {
        // Return sorted set (lexicographical).
        final Set<OpDeclNode> unassignedVars = new TreeSet<>(Comparator.comparing(o -> o.getName().toString()));
        final int len = this.values.length;
        for (int i = 0; i < len; i++) {
            if (values[i] == null) {
                unassignedVars.add(vars[i]);
            }
        }
        return unassignedVars;
    }

    // *********//

    @Override
    public void write(final IValueOutputStream vos) throws IOException {
        super.write(vos);
        for (final IValue value : this.values) {
            value.write(vos);
        }
    }

    /* Returns a string representation of this state.  */
    public String toString() {
        if (TLCGlobals.useView && viewMap != null) {
            final IValue val = mytool.eval(viewMap, Context.Empty, this);
            return viewMap.toString(val);
        }
        final StringBuilder result = new StringBuilder();
        final int vlen = vars.length;
        if (vlen == 1) {
            final UniqueString key = vars[0].getName();
            final IValue val = this.lookup(key);
            result.append(key);
            result.append(" = ");
            result.append(Values.ppr(val));
            result.append("\n");
        } else {
            for (final OpDeclNode var : vars) {
                final UniqueString key = var.getName();
                final IValue val = this.lookup(key);
                result.append("/\\ ");
                result.append(key);
                result.append(" = ");
                result.append(Values.ppr(val));
                result.append("\n");
            }
        }
        return result.toString();
    }

    /* Returns a string representation of this state.  */
    @Override
    public String toString(final TLCState lastState) {
        final StringBuilder result = new StringBuilder();
        final TLCStateMutExt lstate = (TLCStateMutExt) lastState;

        final int vlen = vars.length;
        if (vlen == 1) {
            final UniqueString key = vars[0].getName();
            final IValue val = this.lookup(key);
            final IValue lstateVal = lstate.lookup(key);
            if (!Objects.requireNonNull(lstateVal).equals(val)) {
                result.append(key);
                result.append(" = ").append(Values.ppr(val)).append("\n");
            }
        } else {
            for (final OpDeclNode var : vars) {
                final UniqueString key = var.getName();
                final IValue val = this.lookup(key);
                final IValue lstateVal = lstate.lookup(key);
                if (!Objects.requireNonNull(lstateVal).equals(val)) {
                    result.append("/\\ ");
                    result.append(key);
                    result.append(" = ").append(Values.ppr(val)).append("\n");
                }
            }
        }
        return result.toString();
    }

    // *********//

    @Override
    public Action getAction() {
        return action;
    }

    @Override
    public TLCState setAction(final Action action) {
        this.action = action;
        return this;
    }

    @Override
    public TLCState setPredecessor(final TLCState predecessor) {
        this.predecessor = predecessor;
        return super.setPredecessor(predecessor);
    }

    @Override
    public TLCState getPredecessor() {
        return predecessor;
    }

    // *********//

    @Override
    public TLCState unsetPredecessor() {
        this.predecessor = null;
        return this;
    }

    @Override
    protected TLCState deepCopy(final TLCState copy) {
        super.deepCopy(copy);
        return copyExt(copy);
    }

    // *********//

    private TLCState copyExt(final TLCState copy) {
        if (this.predecessor != null) {
            copy.setPredecessor(this.predecessor);
        }
        return copy.setAction(getAction());
    }

    @Override
    public Object execCallable() throws Exception {
        if (callable != null) {
            return callable.call();
        }
        return null;
    }

    @Override
    public void setCallable(final Callable<?> f) {
        this.callable = f;
    }
}
