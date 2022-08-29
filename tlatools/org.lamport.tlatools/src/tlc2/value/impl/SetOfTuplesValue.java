// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2021, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:18:39 PST by lamport
//      modified on Fri Aug 10 15:09:59 PDT 2001 by yuanyu

package tlc2.value.impl;

import tlc2.TLCGlobals;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;

import java.io.IOException;
import java.util.Objects;

public class SetOfTuplesValue extends EnumerableValue implements Enumerable {
    private static final long serialVersionUID = -1393994948158930526L;
    public final Value[] sets;
    protected SetEnumValue tupleSet;

    /* Constructor */
    public SetOfTuplesValue(final Value[] sets) {
        this.sets = sets;
        this.tupleSet = null;
    }

    public SetOfTuplesValue(final Value[] set, final CostModel cm) {
        this(set);
        this.cm = cm;
    }

    public SetOfTuplesValue(final Value val) {
        this(new Value[1]);
        this.sets[0] = val;
    }

    public SetOfTuplesValue(final Value v1, final Value v2) {
        this(new Value[2]);
        this.sets[0] = v1;
        this.sets[1] = v2;
    }

    @Override
    public final byte getKind() {
        return SETOFTUPLESVALUE;
    }

    @Override
    public final int compareTo(final Object obj) {
        try {
            this.convertAndCache();
            return this.tupleSet.compareTo(obj);
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
            if (obj instanceof final SetOfTuplesValue tvs) {

                final boolean isEmpty1 = this.isEmpty();
                if (isEmpty1) return tvs.isEmpty();
                if (tvs.isEmpty()) return isEmpty1;

                if (this.sets.length != tvs.sets.length) {
                    return false;
                }
                for (int i = 0; i < this.sets.length; i++) {
                    if (!this.sets[i].equals(tvs.sets[i])) {
                        return false;
                    }
                }
                return true;
            }
            this.convertAndCache();
            return this.tupleSet.equals(obj);
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
            final TupleValue tv = (TupleValue) elem.toTuple();
            if (tv == null) {
                final FcnRcdValue fcn = (FcnRcdValue) elem.toFcnRcd();
                if (fcn == null) {
                    if (elem instanceof ModelValue mv)
                        return mv.modelValueMember(this);
                    Assert.fail("Attempted to check if non-tuple\n" + Values.ppr(elem.toString()) +
                            "\nis in the set of tuples:\n" + Values.ppr(this.toString()), getSource());
                }
                if (Objects.requireNonNull(fcn).intv != null) return false;
                for (int i = 0; i < Objects.requireNonNull(fcn.domain).length; i++) {
                    if (!(fcn.domain[i] instanceof IntValue)) {
                        Assert.fail("Attempted to check if non-tuple\n" + Values.ppr(elem.toString()) +
                                "\nis in the set of tuples:\n" + Values.ppr(this.toString()), getSource());
                    }
                }
                return false;
            }
            if (tv.elems.length == this.sets.length) {
                for (int i = 0; i < this.sets.length; i++) {
                    if (!this.sets[i].member(tv.elems[i]))
                        return false;
                }
                return true;
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
            for (final Value set : this.sets) {
                if (!set.isFinite()) {
                    return false;
                }
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
                Assert.fail("Attempted to apply EXCEPT construct to the set of tuples:\n" +
                        Values.ppr(this.toString()), getSource());
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
                Assert.fail("Attempted to apply EXCEPT construct to the set of tuples:\n" +
                        Values.ppr(this.toString()), getSource());
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
            long sz = 1;
            for (final Value set : this.sets) {
                sz *= set.size();
                if (sz < -2147483648 || sz > 2147483647) {
                    Assert.fail("Overflow when computing the number of elements in " +
                            Values.ppr(this.toString()), getSource());
                }
            }
            return (int) sz;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final boolean isNormalized() {
        try {
            if (this.tupleSet == null || this.tupleSet == SetEnumValue.DummyEnum) {
                for (final Value set : this.sets) {
                    if (!set.isNormalized()) {
                        return false;
                    }
                }
                return true;
            }
            return this.tupleSet.isNormalized();
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
            if (this.tupleSet == null || this.tupleSet == SetEnumValue.DummyEnum) {
                for (final Value set : this.sets) {
                    set.normalize();
                }
            } else {
                this.tupleSet.normalize();
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
    public final void deepNormalize() {
        try {
            for (final Value set : sets) {
                set.deepNormalize();
            }
            if (tupleSet == null) {
                tupleSet = SetEnumValue.DummyEnum;
            } else if (tupleSet != SetEnumValue.DummyEnum) {
                tupleSet.deepNormalize();
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
    public final boolean isDefined() {
        try {
            boolean defined = true;
            for (final Value set : this.sets) {
                defined = defined && set.isDefined();
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

    /* The fingerprint  */
    @Override
    public final long fingerPrint(final long fp) {
        try {
            this.convertAndCache();
            return this.tupleSet.fingerPrint(fp);
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
            this.convertAndCache();
            return this.tupleSet.permute(perm);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    private void convertAndCache() {
        if (this.tupleSet == null) {
            this.tupleSet = (SetEnumValue) this.toSetEnum();
        } else if (this.tupleSet == SetEnumValue.DummyEnum) {
            final SetEnumValue val = (SetEnumValue) this.toSetEnum();
            val.deepNormalize();
            this.tupleSet = val;
        }
    }

    @Override
    public final Value toSetEnum() {
        if (this.tupleSet != null && this.tupleSet != SetEnumValue.DummyEnum) {
            return this.tupleSet;
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
    public final void write(final IValueOutputStream vos) throws IOException {
        tupleSet.write(vos);
    }

    /* The string representation of the value. */
    @Override
    public final StringBuilder toString(final StringBuilder sb, final int offset, final boolean swallow) {
        try {
            boolean unlazy = TLCGlobals.expand;
            try {
                if (unlazy) {
                    long sz = 1;
                    for (final Value set : this.sets) {
                        sz *= set.size();
                        if (sz < -2147483648 || sz > 2147483647) {
                            unlazy = false;
                            break;
                        }
                    }
                    unlazy = sz < TLCGlobals.enumBound;
                }
            } catch (final Throwable e) {
                if (swallow) unlazy = false;
                else throw e;
            }

            if (unlazy) {
                final Value val = this.toSetEnum();
                return val.toString(sb, offset, swallow);
            } else {
                if (this.sets.length > 0) {
                    sb.append("(");
                    this.sets[0].toString(sb, offset, swallow);
                }
                for (int i = 1; i < this.sets.length; i++) {
                    sb.append(" \\X ");
                    this.sets[i].toString(sb, offset, swallow);
                }
                if (this.sets.length > 0) {
                    sb.append(")");
                }
                return sb;
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
    public final ValueEnumeration elements() {
        try {
            if (this.tupleSet == null || this.tupleSet == SetEnumValue.DummyEnum) {
                return new Enumerator();
            }
            return this.tupleSet.elements();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    final class Enumerator implements ValueEnumeration {
        private final Value[] currentElems;
        private ValueEnumeration[] enums;
        private boolean isDone;

        public Enumerator() {
            this.enums = new ValueEnumeration[sets.length];
            this.currentElems = new Value[sets.length];
            this.isDone = false;
            for (int i = 0; i < sets.length; i++) {
                if (sets[i] instanceof Enumerable enumerable) {
                    this.enums[i] = enumerable.elements();
                    this.currentElems[i] = this.enums[i].nextElement();
                    if (this.currentElems[i] == null) {
                        this.enums = null;
                        this.isDone = true;
                        break;
                    }
                } else {
                    Assert.fail("Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn," +
                            "\nbut can't enumerate s" + i + ":\n" + Values.ppr(sets[i].toString()), getSource());
                }
            }
        }

        @Override
        public void reset() {
            if (this.enums != null) {
                for (int i = 0; i < this.enums.length; i++) {
                    this.enums[i].reset();
                    this.currentElems[i] = this.enums[i].nextElement();
                }
                this.isDone = false;
            }
        }

        @Override
        public Value nextElement() {
            if (this.isDone) return null;
            final Value[] elems = new Value[this.currentElems.length];
            if (coverage) {
                cm.incSecondary(elems.length);
            }
            System.arraycopy(this.currentElems, 0, elems, 0, elems.length);
            for (int i = elems.length - 1; i >= 0; i--) {
                this.currentElems[i] = this.enums[i].nextElement();
                if (this.currentElems[i] != null) break;
                if (i == 0) {
                    this.isDone = true;
                    break;
                }
                this.enums[i].reset();
                this.currentElems[i] = this.enums[i].nextElement();
            }
            return new TupleValue(elems, cm);
        }
    }

}
