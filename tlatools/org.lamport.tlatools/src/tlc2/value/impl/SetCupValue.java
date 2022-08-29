// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2021, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:21:03 PST by lamport
//      modified on Fri Aug 10 15:09:28 PDT 2001 by yuanyu

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

public class SetCupValue extends EnumerableValue implements Enumerable {
    private static final long serialVersionUID = -3722888493173106476L;
    public final Value set1;
    public final Value set2;
    protected SetEnumValue cupSet;

    /* Constructor */
    public SetCupValue(final Value set1, final Value set2) {
        this.set1 = set1;
        this.set2 = set2;
        this.cupSet = null;
    }

    public SetCupValue(final Value set1, final Value set2, final CostModel cm) {
        this(set1, set2);
        this.cm = cm;
    }

    @Override
    public final byte getKind() {
        return SETCUPVALUE;
    }

    @Override
    public final int compareTo(final Object obj) {
        try {
            this.convertAndCache();
            return this.cupSet.compareTo(obj);
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
            this.convertAndCache();
            return this.cupSet.equals(obj);
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
            return this.set1.member(elem) || this.set2.member(elem);
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
            return this.set1.isFinite() && this.set2.isFinite();
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
            this.convertAndCache();
            return this.cupSet.size();
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
            return (this.cupSet != null &&
                    this.cupSet != SetEnumValue.DummyEnum &&
                    this.cupSet.isNormalized());
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
            if (this.cupSet != null && this.cupSet != SetEnumValue.DummyEnum) {
                this.cupSet.normalize();
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
            set1.deepNormalize();
            set2.deepNormalize();
            if (cupSet == null) {
                cupSet = SetEnumValue.DummyEnum;
            } else if (cupSet != SetEnumValue.DummyEnum) {
                cupSet.deepNormalize();
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
            return this.set1.isDefined() && this.set2.isDefined();
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

    @Override
    public final void write(final IValueOutputStream vos) throws IOException {
        cupSet.write(vos);
    }

    /* The fingerprint methods */
    @Override
    public final long fingerPrint(final long fp) {
        try {
            this.convertAndCache();
            return this.cupSet.fingerPrint(fp);
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
            return this.cupSet.permute(perm);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    private void convertAndCache() {
        if (this.cupSet == null) {
            this.cupSet = (SetEnumValue) this.toSetEnum();
        } else if (this.cupSet == SetEnumValue.DummyEnum) {
            final SetEnumValue val = (SetEnumValue) this.toSetEnum();
            val.deepNormalize();
            this.cupSet = val;
        }
    }

    @Override
    public final Value toSetEnum() {
        if (this.cupSet != null && this.cupSet != SetEnumValue.DummyEnum) {
            return this.cupSet;
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
        return new SetEnumValue(vals, false, cm);
    }

    /* String representation of the value. */
    @Override
    public final StringBuilder toString(StringBuilder sb, final int offset, final boolean swallow) {
        try {
            try {
                if (TLCGlobals.expand) {
                    final Value val = this.toSetEnum();
                    return val.toString(sb, offset, swallow);
                }
            } catch (final Throwable e) {
                if (!swallow) throw e;
            }

            sb = this.set1.toString(sb, offset, swallow);
            sb.append(" \\cup ");
            sb = this.set2.toString(sb, offset, swallow);
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
            if (this.cupSet == null || this.cupSet == SetEnumValue.DummyEnum) {
                return new Enumerator();
            }
            return this.cupSet.elements();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }

    }

    final class Enumerator implements ValueEnumeration {
        ValueEnumeration enum1;
        ValueEnumeration enum2;

        public Enumerator() {
            if ((set1 instanceof Enumerable e1) &&
                    (set2 instanceof Enumerable e2)) {
                this.enum1 = e1.elements();
                this.enum2 = e2.elements();
            } else {
                Assert.fail("Attempted to enumerate S \\cup T when S:\n" +
                        Values.ppr(set1.toString()) + "\nand T:\n" + Values.ppr(set2.toString()) +
                        "\nare not both enumerable", getSource());
            }
        }

        @Override
        public void reset() {
            this.enum1.reset();
            this.enum2.reset();
        }

        @Override
        public Value nextElement() {
            if (coverage) {
                cm.incSecondary();
            }
            Value elem = this.enum1.nextElement();
            if (elem != null) return elem;
            elem = this.enum2.nextElement();
            return elem;
        }
    }

}
