// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Thu  5 Jul 2007 at  4:44:23 PST by lamport
//      modified on Fri Aug 10 15:10:04 PDT 2001 by yuanyu

package tlc2.value.impl;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.tool.EvalException;
import tlc2.tool.FingerprintException;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.value.*;
import util.Assert;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

public class SetPredValue extends EnumerableValue implements Enumerable {
    private static final long serialVersionUID = -2758301062935588759L;
    public final Object vars;           // FormalParamNode or FormalParamNode[]
    public final SemanticNode pred;     // the predicate
    public final ITool tool;             // null iff inVal is the real set
    public final Context con;
    public final TLCState state;
    public final TLCState pstate;
    public final int control;
    /***********************************************************************
     * Was OpDeclNode or OpDeclNode[].                                      *
     ***********************************************************************/
    public Value inVal;           // the in value or the real set
    /**
     * true after inVal has been converted to a SetEnumValue.  I assume this
     * implies (inVal instanceof SetEnumValue) too but the serialization
     * might interfere.
     * MAK 07/18/2019
     */
    private boolean converted = false;

    /* Constructor */
    public SetPredValue(final Object vars, final Value inVal, final SemanticNode pred, final ITool tool,
                        final Context con, final TLCState s0, final TLCState s1, final int control) {
        this.vars = vars;
        this.inVal = inVal;
        this.pred = pred;
        this.tool = tool;
        this.con = con;
        this.state = s0.copy();
        if (s1 != null) {
            this.pstate = s1.copy();
        } else {
            this.pstate = null;
        }
        /**
         * The two copy()s above were added by YY on 12 Mar 2010 to fix the
         * following bug: When a lazily evaluated expression is saved, the
         * state under which it should be evaluated must be saved.  The
         * s0 and s1 objects with which this method is called can be modified
         * after the call, so copies must be made.
         */
        this.control = control;
    }

    public SetPredValue(final Object vars, final Value inVal, final SemanticNode pred, final ITool tool,
                        final Context con, final TLCState s0, final TLCState s1, final int control, final CostModel cm) {
        this(vars, inVal, pred, tool, con, s0, s1, control);
        this.cm = cm;
    }

    public SetPredValue(final SetPredValue other, final ITool tool) {
        this(other.vars, other.inVal, other.pred, tool, other.con, other.state, other.pstate, other.control, other.cm);
    }

    @Override
    public final byte getKind() {
        return SETPREDVALUE;
    }

    @Override
    public final int compareTo(final Object obj) {
        try {
            this.inVal = this.toSetEnum();
            this.converted = true;
            return this.inVal.compareTo(obj);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    public final boolean equals(final Object obj) {
        try {
            this.inVal = this.toSetEnum();
            this.converted = true;
            return this.inVal.equals(obj);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final boolean member(final Value elem) {
        try {
            if (this.converted) {
                return this.inVal.member(elem);
            }
            try {
                if (this.inVal.member(elem)) {
                    Context con1 = this.con;
                    if (this.vars instanceof FormalParamNode fpm) {
                        con1 = con1.cons(fpm, elem);
                    } else {
                        final FormalParamNode[] ids = (FormalParamNode[]) this.vars;
                        final TupleValue tv = (TupleValue) elem.toTuple();
                        if ((tv != null) && (tv.elems.length == ids.length)) {
                            final Value[] vals = tv.elems;
                            for (int i = 0; i < ids.length; i++) {
                                con1 = con1.cons(ids[i], vals[i]);
                            }
                        } else {
                            Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
                                    "\nis an element of a set of " + ids.length + "-tuples.", getSource());
                        }
                    }
                    final Value res = (Value) this.tool.eval(this.pred, con1, this.state, this.pstate, this.control);
                    if (!(res instanceof IBoolValue)) {
                        Assert.fail("The evaluation of predicate " + this.pred +
                                " yielded non-Boolean value.", getSource());
                    }
                    return ((BoolValue) res).val;
                }
            } catch (final EvalException e) {
                Assert.fail("Cannot decide if element:\n" + Values.ppr(elem.toString()) +
                        "\n is element of:\n" + Values.ppr(this.inVal.toString()) +
                        "\nand satisfies the predicate " + this.pred, getSource());
            }
            return false;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final boolean isFinite() {
        try {
            if (!(this.inVal.isFinite())) {
                Assert.fail("Attempted to check if expression of form {x \\in S : p(x)} is a " +
                        "finite set, but cannot check if S:\n" + Values.ppr(this.inVal.toString()) +
                        "\nis finite.", getSource());
            }
            return true;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value takeExcept(final ValueExcept ex) {
        try {
            if (ex.idx < ex.path.length) {
                Assert.fail("Attempted to apply EXCEPT to the set " + Values.ppr(this.toString()) + ".", getSource());
            }
            return ex.value;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value takeExcept(final ValueExcept[] exs) {
        try {
            if (exs.length != 0) {
                Assert.fail("Attempted to apply EXCEPT to the set " + Values.ppr(this.toString()) + ".", getSource());
            }
            return this;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final int size() {
        try {
            this.inVal = this.toSetEnum();
            this.converted = true;
            return this.inVal.size();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    private void readObject(final ObjectInputStream ois) throws IOException, ClassNotFoundException {
        this.inVal = (Value) ois.readObject();
        this.converted = true;
    }

    private void writeObject(final ObjectOutputStream oos) throws IOException {
        if (!this.converted) {
            this.inVal = this.toSetEnum();
            this.converted = true;
        }
        oos.writeObject(this.inVal);
    }

    /* This method normalizes (destructively) this set. */
    @Override
    public final boolean isNormalized() {
        try {
            return this.inVal.isNormalized();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value normalize() {
        try {
            this.inVal.normalize();
            return this;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final void deepNormalize() {
        try {
            inVal.deepNormalize();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final boolean isDefined() {
        return true;
    }

    @Override
    public final IValue deepCopy() {
        return this;
    }

    @Override
    public final boolean assignable(final Value val) {
        try {
            return this.equals(val);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /* The fingerprint method */
    @Override
    public final long fingerPrint(final long fp) {
        try {
            this.inVal = this.toSetEnum();
            this.converted = true;
            return this.inVal.fingerPrint(fp);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final IValue permute(final IMVPerm perm) {
        try {
            this.inVal = this.toSetEnum();
            this.converted = true;
            return this.inVal.permute(perm);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public Value toSetEnum() {
        if (this.converted) {
            return this.inVal;
        }
        final ValueVec vals = new ValueVec();
        final ValueEnumeration Enum = this.elements();
        Value elem;
        while ((elem = Enum.nextElement()) != null) {
            vals.add(elem);
        }
        if (coverage) {
            cm.incSecondary(vals.size());
        }
        return new SetEnumValue(vals, this.isNormalized(), cm);
    }

    @Override
    public void write(final IValueOutputStream vos) throws IOException {
        inVal.write(vos);
    }

    /* The string representation of the value. */
    @Override
    public final StringBuilder toString(final StringBuilder sb, final int offset, final boolean swallow) {
        try {
            try {
                if (TLCGlobals.expand) {
                    final Value val = this.toSetEnum();
                    return val.toString(sb, offset, swallow);
                }
            } catch (final Throwable e) {
                if (!swallow) throw e;
            }

            sb.append("{");
            if (this.vars instanceof FormalParamNode fpm) {
                sb.append(fpm.getName());
            } else {
                final FormalParamNode[] ids = (FormalParamNode[]) this.vars;
                if (ids.length != 0) sb.append(ids[0].getName());
                for (int i = 1; i < ids.length; i++) {
                    sb.append(", ").append(ids[i].getName());
                }
            }
            sb.append(" \\in ").append(this.inVal).append(" : <expression ");
            sb.append(this.pred).append("> }");
            return sb;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final ValueEnumeration elements() {
        try {
            if (this.converted) {
                return ((SetEnumValue) this.inVal).elements();
            }
            return new Enumerator();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    final class Enumerator implements ValueEnumeration {
        final ValueEnumeration Enum;

        public Enumerator() {
            if (inVal instanceof Enumerable enumerable) {
                this.Enum = enumerable.elements();
            } else {
                Assert.fail("Attempted to enumerate { x \\in S : p(x) } when S:\n" +
                        Values.ppr(inVal.toString()) + "\nis not enumerable", getSource());
                throw new RuntimeException("Placeholder for Assert");
            }
        }

        @Override
        public void reset() {
            this.Enum.reset();
        }

        @Override
        public Value nextElement() {
            Value elem;
            while ((elem = this.Enum.nextElement()) != null) {
                if (coverage) {
                    cm.incSecondary();
                }
                Context con1 = con;
                if (vars instanceof FormalParamNode fpm) {
                    con1 = con1.cons(fpm, elem);
                } else {
                    final FormalParamNode[] ids = (FormalParamNode[]) vars;
                    final TupleValue tv = (TupleValue) elem.toTuple();
                    if ((tv != null) &&
                            (tv.elems.length == ids.length)) {
                        final Value[] vals = tv.elems;
                        for (int i = 0; i < ids.length; i++) {
                            con1 = con1.cons(ids[i], vals[i]);
                        }
                    } else {
                        Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
                                "\nis an element of a set of " + ids.length + "-tuples.", getSource());
                    }
                }
                final Value res = (Value) tool.eval(pred, con1, state, pstate, control, cm);
                if (!(res instanceof IBoolValue)) {
                    Assert.fail("Evaluating predicate " + pred + " yielded non-Boolean value.", getSource());
                }
                if (((BoolValue) res).val) return elem;
            }
            return null;
        }

    }

}
