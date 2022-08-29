// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:57 PST by lamport
//      modified on Fri Mar  2 15:37:34 PST 2001 by yuanyu

package tlc2.tool;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;

/*
 * This class represents a TLA+ state vector.
 * This is the mutable version, which means that in-place
 * updates are used for improved performance and reduced
 * allocation.
 */
public final class StateVec extends ArrayList<TLCState> implements IStateFunctor, INextStateFunctor {
    public StateVec(int length) {
        super(length);
    }

    public StateVec(TLCState[] states) {
        this.addAll(Arrays.asList(states));
    }

    public boolean isLastElement(final TLCState state) {
        if (isEmpty()) {
            return false;
        }
        return this.get(size() - 1) == state;
    }

    public TLCState first() {
        return get(0);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.IStateFunction#addElement(tlc2.tool.TLCState)
     */
    public StateVec addState(TLCState state) {
        this.add(state);
        return this;
    }

    @Override
    public StateVec addState(TLCState predecessor, Action action, TLCState state) {
        return addState(state.setPredecessor(predecessor).setAction(action));
    }

    public void deepNormalize() {
        for (var state : this) {
            state.deepNormalize();
        }
    }

    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("{");
        if (this.size() > 0) {
            sb.append(this.get(0).toString());
        }
        for (int i = 1; i < this.size(); i++) {
            sb.append(", ");
            sb.append(this.get(i).toString());
        }
        sb.append("}");
        return sb.toString();
    }

    public boolean contains(final TLCState state) {
        return this.stream().anyMatch(s -> s.fingerPrint() == state.fingerPrint());
    }

    /***
     * This function is defined to remove elements in the same way as other data structures, to maintain index consistency
     * @param index
     */
    public void removeIndexMovingLastElement(final int index){
        final int lastIndex = size()-1;

        Collections.swap(this, index, lastIndex);
        this.remove(lastIndex);
    }

    @Override
    public boolean hasStates() {
        return !isEmpty();
    }
}