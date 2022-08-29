// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 15:30:09 PST by lamport
//      modified on Fri Aug 10 15:10:22 PDT 2001 by yuanyu

package tlc2.value.impl;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.EvalControl;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.util.FP64;
import tlc2.value.*;
import util.Assert;
import util.UniqueString;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;

public class TupleValue extends Value implements Applicable, ITupleValue {
    public static final TupleValue EmptyTuple = new TupleValue(new Value[0]);
    private static final long serialVersionUID = 5004755628424465591L;
    public final Value[] elems;          // the elements of this tuple.

    /* Constructor */
    public TupleValue(final Value[] elems) {
        this.elems = elems;
    }

    public TupleValue(final Value v) {
        this(new Value[1]);
        this.elems[0] = v;
    }

    public TupleValue(final Value v1, final Value v2) {
        this(new Value[2]);
        this.elems[0] = v1;
        this.elems[1] = v2;
    }

    public TupleValue(final Value[] elems, final CostModel cm) {
        this(elems);
        this.cm = cm;
    }

    public static IValue createFrom(final IValueInputStream vos) throws IOException {
        final int index = vos.getIndex();
        final int len = vos.readNat();
        final Value[] elems = new Value[len];
        for (int i = 0; i < len; i++) {
            elems[i] = (Value) vos.read();
        }
        final Value res = new TupleValue(elems);
        vos.assign(res, index);
        return res;
    }

    public static IValue createFrom(final ValueInputStream vos, final Map<String, UniqueString> tbl) throws IOException {
        final int index = vos.getIndex();
        final int len = vos.readNat();
        final Value[] elems = new Value[len];
        for (int i = 0; i < len; i++) {
            elems[i] = (Value) vos.read(tbl);
        }
        final Value res = new TupleValue(elems);
        vos.assign(res, index);
        return res;
    }

    @Override
    public IValue getElem(final int idx) {
        return elems[idx];
    }

    @Override
    public IValue[] getElems() {
        return elems;
    }

    @Override
    public final byte getKind() {
        return TUPLEVALUE;
    }

    @Override
    public final int compareTo(final Object obj) {
        try {
            final TupleValue tv = obj instanceof Value v ? (TupleValue) v.toTuple() : null;
            if (tv == null) {
                // Well, we have to convert this to function and compare.
                return this.toFcnRcd().compareTo(obj);
            }
            final int len = this.elems.length;
            int cmp = len - tv.elems.length;
            if (cmp == 0) {
                // At this point, we know that the domains are equal because the domain of a
                // tuple is 1..N where N is Len(tuple). Thus, we can compare the values one by
                // one.
                for (int i = 0; i < len; i++) {
                    cmp = this.elems[i].compareTo(tv.elems[i]);
                    if (cmp != 0) break;
                }
            }
            return cmp;
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
            final TupleValue tv = obj instanceof Value v ? (TupleValue) v.toTuple() : null;
            if (tv == null) {
                // Well, we have to convert this to function and compare.
                return this.toFcnRcd().equals(obj);
            }
            final int len = this.elems.length;
            if (len != tv.elems.length)
                return false;
            // At this point, we know that the domains are equal because the domain of a
            // tuple is 1..N where N is Len(tuple). Thus, we can check equality of the
            // values one by one.
            for (int i = 0; i < len; i++) {
                if (!this.elems[i].equals(tv.elems[i]))
                    return false;
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
    public final boolean member(final Value elem) {
        try {
            Assert.fail("Attempted to check set membership in a tuple value.", getSource());
            return false;   // make compiler happy
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
        return true;
    }

    @Override
    public final Value apply(final Value arg, final int control) {
        try {
            if (arg instanceof IntValue iv) {
                final int idx = iv.val;

                if (idx <= 0 || idx > this.elems.length) {
                    Assert.fail("Attempted to access index " + idx + " of tuple\n"
                            + Values.ppr(this.toString()) + "\nwhich is out of bounds.", getSource());
                }
                return this.elems[idx - 1];
            } else {
                Assert.fail("Attempted to access tuple at a non integral index: " + Values.ppr(arg.toString()), getSource());
                throw new RuntimeException("Placeholder for Assert");
            }
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value apply(final Value[] args, final int control) {
        try {
            if (args.length != 1) {
                Assert.fail("Attempted to access tuple with " + args.length + " arguments when it expects 1.", getSource());
            }
            return this.apply(args[0], EvalControl.Clear);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value select(final Value arg) {
        try {
            if (arg instanceof IntValue iv) {
                final int idx = iv.val;
                if (idx > 0 && idx <= this.elems.length) {
                    return this.elems[idx - 1];
                }
                return null;
            } else {
                Assert.fail("Attempted to access tuple at a non integral index: " + Values.ppr(arg.toString()), getSource());
                throw new RuntimeException("Placeholder for Assert");
            }
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
                final int tlen = this.elems.length;
                final Value[] newElems = new Value[tlen];
                final Value arcVal = ex.path[ex.idx];
                if (arcVal instanceof IntValue iv) {
                    final int idx = iv.val - 1;
                    if (0 <= idx && idx < tlen) {
                        System.arraycopy(this.elems, 0, newElems, 0, tlen);
                        ex.idx++;
                        newElems[idx] = this.elems[idx].takeExcept(ex);
                    }
                    return new TupleValue(newElems);
                }
                MP.printWarning(EC.TLC_WRONG_TUPLE_FIELD_NAME, new String[]{Values.ppr(arcVal.toString())});
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
            Value val = this;
            for (final ValueExcept ex : exs) {
                val = val.takeExcept(ex);
            }
            return val;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value getDomain() {
        try {
            return new IntervalValue(1, this.size());
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
        return this.elems.length;
    }

    @Override
    public final void deepNormalize() {
        try {
            for (final Value elem : elems) {
                elem.deepNormalize();
            }
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final Value toTuple() {
        return this;
    }

    @Override
    public final Value toRcd() {
        return size() == 0 ? RecordValue.EmptyRcd : super.toRcd();
    }

    @Override
    public final Value toFcnRcd() {
        final IntervalValue intv = new IntervalValue(1, this.elems.length);
        if (coverage) {
            cm.incSecondary(this.elems.length);
        }
        return new FcnRcdValue(intv, this.elems, cm);
    }

    /* The normalization of the value. */
    @Override
    public final boolean isNormalized() {
        return true;
    }

    @Override
    public final Value normalize() { /*nop*/
        return this;
    }

    @Override
    public final boolean isDefined() {
        try {
            boolean defined = true;
            for (final Value elem : this.elems) {
                defined = defined && elem.isDefined();
            }
            return defined;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final IValue deepCopy() {
        try {
            final Value[] vals = new Value[this.elems.length];
            for (int i = 0; i < this.elems.length; i++) {
                vals[i] = (Value) this.elems[i].deepCopy();
            }
            return new TupleValue(vals);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final boolean assignable(final Value val) {
        try {
            boolean canAssign = ((val instanceof TupleValue tv) &&
                    (this.elems.length == tv.elems.length));
            if (!canAssign) return false;
            for (int i = 0; i < this.elems.length; i++) {
                canAssign = canAssign && this.elems[i].assignable(((TupleValue) val).elems[i]);
            }
            return canAssign;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final void write(final IValueOutputStream vos) throws IOException {
        final int index = vos.put(this);
        if (index == -1) {
            vos.writeByte(TUPLEVALUE);
            final int len = elems.length;
            vos.writeNat(len);
            for (final Value elem : elems) {
                elem.write(vos);
            }
        } else {
            vos.writeByte(DUMMYVALUE);
            vos.writeNat(index);
        }
    }

    /* The fingerprint method: tuples are functions. */
    @Override
    public final long fingerPrint(long fp) {
        try {
            final int len = this.elems.length;
            fp = FP64.Extend(fp, FCNRCDVALUE);
            fp = FP64.Extend(fp, len);
            for (int i = 0; i < len; i++) {
                fp = FP64.Extend(fp, INTVALUE);
                fp = FP64.Extend(fp, i + 1);
                fp = this.elems[i].fingerPrint(fp);
            }
            return fp;
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
            final Value[] vals = new Value[this.elems.length];
            boolean changed = false;
            for (int i = 0; i < vals.length; i++) {
                vals[i] = (Value) this.elems[i].permute(perm);
                changed = changed || (vals[i] != this.elems[i]);
            }
            if (changed) {
                return new TupleValue(vals);
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

    /* The string representation of this value. */
    @Override
    public final StringBuilder toString(StringBuilder sb, final int offset, final boolean swallow) {
        try {
            sb.append("<<");
            final int len = this.elems.length;
            if (len > 0) {
                sb = this.elems[0].toString(sb, offset, swallow);
            }
            for (int i = 1; i < len; i++) {
                sb.append(", ");
                sb = this.elems[i].toString(sb, offset, swallow);
            }
            sb.append(">>");
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
    public List<TLCVariable> getTLCVariables(final TLCVariable prototype, final Random rnd) {
        final List<TLCVariable> nestedVars = new ArrayList<>(this.size());
        for (int i = 0; i < elems.length; i++) {
            final Value value = elems[i];
            final TLCVariable nested = prototype.newInstance(Integer.toString(i + 1), value, rnd);
            nested.setValue(value.toString());
            nested.setType(value.getTypeString());
            nestedVars.add(nested);
        }
        return nestedVars;
    }
}
