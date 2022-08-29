// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:58 PST by lamport
//      modified on Fri Jul 20 23:54:51 PDT 2001 by yuanyu

package tlc2.tool;

import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.SymbolNode;
import tlc2.value.IValue;
import tlc2.value.IValueInputStream;
import tlc2.value.IValueOutputStream;
import util.UniqueString;
import util.WrongInvocationException;

import java.util.HashSet;
import java.util.Set;

/**
 * This class represents a TLA+ state, which simply is an assignment
 * of explicit values to the variables. This is the functional
 * version.  It is used for implementing the enabled predicate.  It
 * can not be used in getInitStates and getNextStates.
 */
public final class TLCStateFun extends TLCState {
    public static final TLCState Empty = new TLCStateFun(null, null, null);
    private static final long serialVersionUID = -357349115038775307L;
    private final SymbolNode name;
    private final IValue value;
    private final TLCStateFun next;

    private TLCStateFun(final SymbolNode name, final IValue value, final TLCStateFun state) {
        super(new OpDeclNode[]{});
        this.name = name;
        this.value = value;
        this.next = state;
    }

    @Override
    public TLCState createEmpty() {
        return Empty;
    }

    @Override
    public TLCState bind(final UniqueString name, final IValue value) {
        throw new WrongInvocationException("TLCStateFun.bind: This is a TLC bug.");
    }

    @Override
    public TLCState bind(final SymbolNode id, final IValue value) {
        return new TLCStateFun(id, value, this);
    }

    @Override
    public TLCState unbind(final UniqueString name) {
        throw new WrongInvocationException("TLCStateFun.unbind: This is a TLC bug.");
    }

    @Override
    public IValue lookup(final UniqueString var) {
        for (TLCStateFun cur = this; cur != Empty; cur = cur.next) {
            if (var == cur.name.getName()) return cur.value;
        }
        return null;
    }

    @Override
    public boolean containsKey(final UniqueString var) {
        return this.lookup(var) != null;
    }

    @Override
    public TLCState copy() {
        // The following code added blindly by LL on 28 May 2010
        // to fix a bug.  I have no idea what's going on here.
        return new TLCStateFun(this.name, this.value, this.next);
        // throw new WrongInvocationException("TLCStateFun.copy: This is a TLC bug.");
    }

    @Override
    public TLCState deepCopy() {
        throw new WrongInvocationException("TLCStateFun.deepCopy: This is a TLC bug.");
    }

    @Override
    public void deepNormalize() {
        throw new WrongInvocationException("TLCStateFun.normalizeFcns: This is a TLC bug.");
    }

    @Override
    public long fingerPrint() {
        throw new WrongInvocationException("TLCStateFun.fingerPrint: This is a TLC bug.");
    }

    @Override
    public TLCState createNewFromValueStream(final IValueInputStream vis) {
        throw new WrongInvocationException("TLCStateFun.fingerPrint: This is a TLC bug.");
    }

    @Override
    public boolean allAssigned() {
        return true;
    }

    @Override
    public Set<OpDeclNode> getUnassigned() {
        return new HashSet<>();
    }


    @Override
    public StateVec addToVec(final StateVec states) {
        return states.addState(this);
    }

    @Override
    public void write(final IValueOutputStream vos) {
        throw new WrongInvocationException("TLCStateFun.write: This is a TLC bug.");
    }

    /* Returns a string representation of this state.  */
    public String toString() {
        final StringBuilder sb = new StringBuilder("[");
        if (this != Empty) {
            sb.append(this.name.getName().toString());
            sb.append(" -> ");
            sb.append(this.value.toString());

            for (TLCStateFun cur = this.next; cur != Empty; cur = cur.next) {
                sb.append(", ");
                sb.append(cur.name.getName().toString());
                sb.append("->");
                sb.append(cur.value);
            }
        }
        sb.append("]");
        return sb.toString();
    }

    @Override
    public String toString(final TLCState lastState) {
        throw new WrongInvocationException("TLCStateFun.toString: This is a TLC bug.");
    }

}
