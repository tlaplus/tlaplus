// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2021, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:46:50 PST by lamport
//      modified on Fri Aug 10 15:10:39 PDT 2001 by yuanyu

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

public class UnionValue extends EnumerableValue implements Enumerable {
    private static final long serialVersionUID = 2254984769923081449L;
    public final Value set;
    protected SetEnumValue realSet;

    /* Constructor */
    public UnionValue(final Value set) {
        this.set = set;
        this.realSet = null;
    }

    public UnionValue(final Value val, final CostModel cm) {
        this(val);
        this.cm = cm;
    }

    public static Value union(final Value val) {
        boolean canCombine = (val instanceof SetEnumValue);
        if (canCombine) {
            final ValueVec elems = ((SetEnumValue) val).elems;
            for (int i = 0; i < elems.size(); i++) {
                canCombine = (canCombine &&
                        (elems.get(i) instanceof SetEnumValue));
            }
            if (canCombine) {
                final ValueVec resElems = new ValueVec();
                final Value result = new SetEnumValue(resElems, false, val.getCostModel());
                for (int i = 0; i < elems.size(); i++) {
                    final ValueVec elems1 = ((SetEnumValue) elems.get(i)).elems;
                    for (int j = 0; j < elems1.size(); j++) {
                        final Value elem = elems1.get(j);
                        if (!result.member(elem)) {
                            resElems.add(elem);
                        }
                    }
                }
                return result;
            }
        }
        return new UnionValue(val, val.getCostModel());
    }

    @Override
    public byte getKind() {
        return UNIONVALUE;
    }

    @Override
    public final int compareTo(final Object obj) {
        try {
            this.convertAndCache();
            return this.realSet.compareTo(obj);
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
            return this.realSet.equals(obj);
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
            if (this.set instanceof Enumerable enumerable) {
                final ValueEnumeration Enum = enumerable.elements();
                Value val;
                while ((val = Enum.nextElement()) != null) {
                    if (val.member(elem)) return true;
                }
                return false;
            } else {
                Assert.fail("Attempted to check if:\n " + Values.ppr(elem.toString()) +
                        "\nis an element of the non-enumerable set:\n " +
                        Values.ppr(this.toString()), getSource());
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
    public final boolean isFinite() {
        try {
            if (this.set instanceof Enumerable enumerable) {
                final ValueEnumeration Enum = ((Enumerable) this.set).elements();
                Value val;
                while ((val = Enum.nextElement()) != null) {
                    if (!val.isFinite()) return false;
                }
                return true;
            } else {
                Assert.fail("Attempted to check if the nonenumerable set:\n" + Values.ppr(this.toString()) +
                        "\nis a finite set.", getSource());
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
                Assert.fail("Attempted to apply EXCEPT to the set:\n" + Values.ppr(this.toString()), getSource());
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
                Assert.fail("Attempted to apply EXCEPT to the set:\n " + Values.ppr(this.toString()) + ".", getSource());
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
            return this.realSet.size();
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
            return (this.realSet != null &&
                    this.realSet != SetEnumValue.DummyEnum &&
                    this.realSet.isNormalized());
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
            if (this.realSet != null && this.realSet != SetEnumValue.DummyEnum) {
                this.realSet.normalize();
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
            // MAK 09/17/2019: Added call to this.set.deepNormalize() to align with pattern
            // generally found in overwrites of Value#deepNormalize.
            // This omission surfaced through a race condition that led to a spurious
            // safety violation (https://github.com/tlaplus/tlaplus/issues/361):
            // 1) A TLA+ spec defines a (zero-arity) operator s.a. "Foo == UNION { ... }"
            //    that appears in an invariant.
            // 2) SpecProcessor#processConstantDefns eagerly evaluates the operator Foo at startup
            //    and inserts its Value result UV into the corresponding node of the semantic graph.
            // 3) Two workers check if two states violate the invariant which triggers UnionValue#member,
            //    which internally causes this.set to be normalized.  Since Value instances are not thread-safe
            //    because they are expected to be fully normalized during state space exploration, the
            //    two workers race to normalize this.set.
            // 4) Worker A gets ahead and loops over the elements in UV#member while worker B still normalizes UV.
            //    Worker A reads inconsistent data and thus reports the invariant to be violated.
            // Thanks to Calvin Loncaric for suggesting this fix.
            this.set.deepNormalize();

            if (realSet == null) {
                realSet = SetEnumValue.DummyEnum;
            } else if (realSet != SetEnumValue.DummyEnum) {
                realSet.deepNormalize();
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
            return this.set.isDefined();
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
    public void write(final IValueOutputStream vos) throws IOException {
        realSet.write(vos);
    }

    /* The fingerprint  */
    @Override
    public final long fingerPrint(final long fp) {
        try {
            this.convertAndCache();
            return this.realSet.fingerPrint(fp);
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
            return this.realSet.permute(perm);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    private void convertAndCache() {
        if (this.realSet == null) {
            this.realSet = (SetEnumValue) this.toSetEnum();
        } else if (this.realSet == SetEnumValue.DummyEnum) {
            final SetEnumValue val = (SetEnumValue) this.toSetEnum();
            val.deepNormalize();
            this.realSet = val;
        }
    }

    @Override
    public final Value toSetEnum() {
        if (this.realSet != null && this.realSet != SetEnumValue.DummyEnum) {
            return this.realSet;
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

    /* String representation of this value. */
    @Override
    public final StringBuilder toString(StringBuilder sb, final int offset, final boolean swallow) {
        try {
            if (TLCGlobals.expand) {
                final Value val = this.toSetEnum();
                return val.toString(sb, offset, swallow);
            } else {
                sb.append("UNION(");
                sb = this.set.toString(sb, offset, swallow);
                sb.append(")");
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
            if (this.realSet == null || this.realSet == SetEnumValue.DummyEnum) {
                return new Enumerator();
            }
            return this.realSet.elements();
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
        Value elemSet;
        ValueEnumeration elemSetEnum;

        public Enumerator() {
            if (set instanceof Enumerable enumerable) {
                this.Enum = enumerable.elements();
                this.elemSet = this.Enum.nextElement();
                if (this.elemSet != null) {
                    if (!(this.elemSet instanceof Enumerable)) {
                        Assert.fail("Attempted to enumerate UNION(s), but some element of s is nonenumerable.", getSource());
                    }
                    this.elemSetEnum = ((Enumerable) this.elemSet).elements();
                }
            } else {
                Assert.fail("Attempted to enumerate the nonenumerable set:\n" +
                        Values.ppr(this.toString()), getSource());
                throw new RuntimeException("Placeholder for Assert");
            }
        }

        @Override
        public void reset() {
            this.Enum.reset();
            this.elemSet = this.Enum.nextElement();
            this.elemSetEnum = ((Enumerable) this.elemSet).elements();
        }

        @Override
        public Value nextElement() {
            if (this.elemSet == null) return null;
            Value val = this.elemSetEnum.nextElement();
            if (val == null) {
                this.elemSet = this.Enum.nextElement();
                if (this.elemSet == null) return null;
                if (!(this.elemSet instanceof Enumerable)) {
                    Assert.fail("Attempted to enumerate the nonenumerable set:\n" +
                            Values.ppr(this.elemSet.toString()) +
                            "\nwhen enumerating:\n" + Values.ppr(this.toString()), getSource());
                }
                this.elemSetEnum = ((Enumerable) this.elemSet).elements();
                val = this.nextElement();
            }
            if (coverage) {
                cm.incSecondary();
            }
            return val;
        }

    }

}
