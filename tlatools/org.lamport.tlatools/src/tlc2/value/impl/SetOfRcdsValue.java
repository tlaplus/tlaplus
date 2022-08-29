// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2021, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:18:01 PST by lamport
//      modified on Fri Aug 10 15:09:53 PDT 2001 by yuanyu

package tlc2.value.impl;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;
import util.UniqueString;

import java.io.IOException;
import java.math.BigInteger;
import java.util.Objects;

public class SetOfRcdsValue extends SetOfFcnsOrRcdsValue implements Enumerable {
    private static final long serialVersionUID = -9092903562165832666L;
    public final UniqueString[] names;      // The names of the fields.
    public final Value[] values;            // The values of the fields.
    protected SetEnumValue rcdSet;

    /* Constructor */
    public SetOfRcdsValue(final UniqueString[] names, final Value[] values, final boolean isNorm) {
        assert names.length == values.length; // see tlc2.tool.Tool.evalAppl(OpApplNode, Context, TLCState, TLCState, int) case for OPCODE_sor
        this.names = names;
        this.values = values;
        this.rcdSet = null;
        if (!isNorm) {
            this.sortByNames();
        }
    }

    public SetOfRcdsValue(final UniqueString[] names, final Value[] values, final boolean isNorm, final CostModel cm) {
        this(names, values, isNorm);
        this.cm = cm;
    }

    @Override
    public final byte getKind() {
        return SETOFRCDSVALUE;
    }

    @Override
    public final int compareTo(final Object obj) {
        try {
            this.convertAndCache();
            return this.rcdSet.compareTo(obj);
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
            if (obj instanceof final SetOfRcdsValue rcds) {

                final boolean isEmpty1 = this.isEmpty();
                if (isEmpty1) {
                    return rcds.isEmpty();
                }
                if (rcds.isEmpty()) {
                    return isEmpty1;
                }

                if (this.names.length != rcds.names.length) {
                    return false;
                }
                for (int i = 0; i < this.names.length; i++) {
                    if (!this.names[i].equals(rcds.names[i]) ||
                            !this.values[i].equals(rcds.values[i])) {
                        return false;
                    }
                }
                return true;
            }
            this.convertAndCache();
            return this.rcdSet.equals(obj);
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
            final RecordValue rcd = (RecordValue) elem.toRcd();
            if (rcd == null) {
                if (elem instanceof ModelValue mv)
                    return mv.modelValueMember(this);
                Assert.fail("Attempted to check if non-record\n" + elem + "\nis in the" +
                        " set of records:\n" + Values.ppr(this.toString()), getSource());
            }
            Objects.requireNonNull(rcd).normalize();
            if (this.names.length != rcd.names.length) {
                return false;
            }
            for (int i = 0; i < this.names.length; i++) {
                if ((!this.names[i].equals(rcd.names[i])) ||
                        (!this.values[i].member(rcd.values[i]))) {
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
    public final boolean isFinite() {
        try {
            for (final Value value : this.values) {
                if (!value.isFinite()) return false;
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
                Assert.fail("Attempted to apply EXCEPT to the set of records:\n" +
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
                Assert.fail("Attempted to apply EXCEPT to the set of records:\n" +
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
            for (final Value value : this.values) {
                sz *= value.size();
                if (sz < -2147483648 || sz > 2147483647) {
                    Assert.fail(EC.TLC_MODULE_OVERFLOW, "the number of elements in:\n" +
                            Values.ppr(this.toString()));
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
    protected boolean needBigInteger() {
        long sz = 1;
        for (final Value value : values) {
            sz *= value.size();
            if (sz < -2147483648 || sz > 2147483647) {
                return true;
            }
        }
        return false;
    }

    @Override
    public final boolean isNormalized() {
        try {
            if (this.rcdSet == null || this.rcdSet == SetEnumValue.DummyEnum) {
                for (int i = 0; i < this.names.length; i++) {
                    if (!this.values[i].isNormalized()) {
                        return false;
                    }
                }
                return true;
            }
            return this.rcdSet.isNormalized();
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
            if (this.rcdSet == null || this.rcdSet == SetEnumValue.DummyEnum) {
                for (int i = 0; i < this.names.length; i++) {
                    this.values[i].normalize();
                }
            } else {
                this.rcdSet.normalize();
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
            for (final Value value : values) {
                value.deepNormalize();
            }
            if (rcdSet == null) {
                rcdSet = SetEnumValue.DummyEnum;
            } else if (rcdSet != SetEnumValue.DummyEnum) {
                rcdSet.deepNormalize();
            }
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    private void sortByNames() {
        for (int i = 1; i < this.names.length; i++) {
            final int cmp = this.names[0].compareTo(this.names[i]);
            if (cmp == 0) {
                Assert.fail("Field name " + this.names[0] + " occurs multiple times" +
                        " in set of records.", getSource());
            } else if (cmp > 0) {
                final UniqueString ts = this.names[0];
                this.names[0] = this.names[i];
                this.names[i] = ts;
                final Value tv = this.values[0];
                this.values[0] = this.values[i];
                this.values[i] = tv;
            }
        }
        for (int i = 2; i < this.names.length; i++) {
            int j = i;
            final UniqueString st = this.names[i];
            final Value val = this.values[i];
            int cmp;
            while ((cmp = st.compareTo(this.names[j - 1])) < 0) {
                this.names[j] = this.names[j - 1];
                this.values[j] = this.values[j - 1];
                j--;
            }
            if (cmp == 0) {
                Assert.fail("Field name " + this.names[i] + " occurs multiple times" +
                        " in set of records.", getSource());
            }
            this.names[j] = st;
            this.values[j] = val;
        }
    }

    @Override
    public final boolean isDefined() {
        try {
            boolean isDefined = true;
            for (final Value value : this.values) {
                isDefined = isDefined && value.isDefined();
            }
            return isDefined;
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
            return this.rcdSet.fingerPrint(fp);
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
            return this.rcdSet.permute(perm);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    private void convertAndCache() {
        if (this.rcdSet == null) {
            this.rcdSet = (SetEnumValue) this.toSetEnum();
        } else if (this.rcdSet == SetEnumValue.DummyEnum) {
            final SetEnumValue val = (SetEnumValue) this.toSetEnum();
            val.deepNormalize();
            this.rcdSet = val;
        }
    }

    @Override
    public final Value toSetEnum() {
        if (this.rcdSet != null && this.rcdSet != SetEnumValue.DummyEnum) {
            return this.rcdSet;
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
        rcdSet.write(vos);
    }

    /* The string representation of the value. */
    @Override
    public final StringBuilder toString(final StringBuilder sb, final int offset, final boolean swallow) {
        try {
            boolean unlazy = TLCGlobals.expand;
            try {
                if (unlazy) {
                    long sz = 1;
                    for (final Value value : this.values) {
                        sz *= value.size();
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
                sb.append("[");
                final int len = this.names.length;
                if (len != 0) {
                    sb.append(names[0]).append(": ");
                    this.values[0].toString(sb, offset, swallow);
                }
                for (int i = 1; i < len; i++) {
                    sb.append(", ");
                    sb.append(names[i]).append(": ");
                    this.values[i].toString(sb, offset, swallow);
                }
                sb.append("]");
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
            if (this.rcdSet == null || this.rcdSet == SetEnumValue.DummyEnum) {
                return new Enumerator();
            }
            return this.rcdSet.elements();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    protected tlc2.value.impl.SetOfFcnsOrRcdsValue.SubsetEnumerator getSubsetEnumerator(final int k, final int n) {
        return new SubsetEnumerator(k, n);
    }

    @Override
    protected BigIntegerSubsetEnumerator getBigSubsetEnumerator(final int k) {
        return new BigIntegerSubsetEnumerator(k);
    }

    final class Enumerator implements ValueEnumeration {
        private final Value[] currentElems;
        private ValueEnumeration[] enums;
        private boolean isDone;

        public Enumerator() {
            this.enums = new ValueEnumeration[values.length];
            this.currentElems = new Value[values.length];
            this.isDone = false;
            for (int i = 0; i < values.length; i++) {
                if (values[i] instanceof Enumerable enumerable) {
                    this.enums[i] = enumerable.elements();
                    this.currentElems[i] = this.enums[i].nextElement();
                    if (this.currentElems[i] == null) {
                        this.enums = null;
                        this.isDone = true;
                        break;
                    }
                } else {
                    Assert.fail("Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn]," +
                            "\nbut can't enumerate the value of the `" + names[i] + "' field:\n" +
                            Values.ppr(values[i].toString()), getSource());
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
            return new RecordValue(names, elems, true, cm);
        }

    }

    class SubsetEnumerator extends SetOfFcnsOrRcdsValue.SubsetEnumerator {

        private final SetEnumValue[] convert;
        private final int[] rescaleBy;

        SubsetEnumerator(final int k, final int n) {
            super(k, n);

            convert = new SetEnumValue[values.length];
            rescaleBy = new int[values.length];

            int numElems = 1; // 1 to avoid div by zero in elementAt
            for (int i = values.length - 1; i >= 0; i--) {
                convert[i] = (SetEnumValue) values[i].toSetEnum();
                rescaleBy[i] = numElems;
                numElems *= convert[i].elems.size();
            }
        }

        @Override
        protected RecordValue get(final int idx) {
            assert 0 <= idx && idx < size();

            final Value[] val = new Value[names.length];
            for (int i = 0; i < val.length; i++) {
                final SetEnumValue sev = convert[i];
                final int mod = sev.elems.size();

                final int rescaledIdx = (int) Math.floor(idx / rescaleBy[i]);
                final int elementAt = rescaledIdx % mod;

                val[i] = sev.elems.get(elementAt);
            }
            return new RecordValue(names, val, false, cm);
        }
    }

    class BigIntegerSubsetEnumerator extends SetOfFcnsOrRcdsValue.BigIntegerSubsetEnumerator {

        private final SetEnumValue[] convert;
        private final BigInteger[] rescaleBy;

        public BigIntegerSubsetEnumerator(final int k) {
            super(k);

            convert = new SetEnumValue[values.length];
            rescaleBy = new BigInteger[values.length];

            BigInteger numElems = BigInteger.ONE; // 1 to avoid div by zero in elementAt
            for (int i = values.length - 1; i >= 0; i--) {
                convert[i] = (SetEnumValue) values[i].toSetEnum();
                rescaleBy[i] = numElems;
                numElems = numElems.multiply(BigInteger.valueOf(convert[i].elems.size()));
            }

            // The size of the (enumerated) SetOfFcnsOrRcdsValue needs BigInteger.
            this.sz = numElems;
        }

        @Override
        protected Value get(final BigInteger idx) {
            final Value[] val = new Value[names.length];
            for (int i = 0; i < val.length; i++) {
                final SetEnumValue sev = convert[i];
                final int mod = sev.elems.size();

                final BigInteger d = idx.divide(rescaleBy[i]);
                final BigInteger m = d.mod(BigInteger.valueOf(mod));
                final int elementAt = m.intValueExact();

                val[i] = sev.elems.get(elementAt);
            }
            return new RecordValue(names, val, false, cm);
        }
    }
}
