// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:07:06 PST by lamport
//      modified on Fri Aug 10 15:07:25 PDT 2001 by yuanyu

package tlc2.value.impl;

import tlc2.tool.EvalControl;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.util.FP64;
import tlc2.value.*;
import util.Assert;
import util.TLAConstants;
import util.ToolIO;
import util.UniqueString;

import java.io.IOException;
import java.util.*;

public class FcnRcdValue extends Value implements Applicable, IFcnRcdValue {

    //  private int[] indexTbl;  // speed up function application
    public static final Value EmptyFcn = new FcnRcdValue(new Value[0], new Value[0], true);
    private static final long serialVersionUID = -5437467086149651742L;
    // -Dtlc2.value.impl.FcnRcdValue.threshold=16
    private static final int LINEAR_SEARCH_THRESHOLD = Integer.getInteger(FcnRcdValue.class.getName() + ".threshold", 32);

    static {
        if (LINEAR_SEARCH_THRESHOLD != 32) {
            ToolIO.out.println("FcnRcdValue#threshold is: " + LINEAR_SEARCH_THRESHOLD);
        }
    }

    public final Value[] domain;
    public final IntervalValue intv;
    public final Value[] values;
    private boolean isNorm;

    /* Constructor */
    public FcnRcdValue(final Value[] domain, final Value[] values, final boolean isNorm) {
        this.domain = domain;
        this.values = values;
        this.intv = null;

        if (!isNorm) {
            this.normalize();
        }
//    this.indexTbl = null;
    }

    public FcnRcdValue(final IntervalValue intv, final Value[] values) {
        this.intv = intv;
        this.values = values;
        this.domain = null;
        this.isNorm = true;
//    this.indexTbl = null;
    }

    public FcnRcdValue(final IntervalValue intv, final Value[] values, final CostModel cm) {
        this(intv, values);
        this.cm = cm;
    }

    private FcnRcdValue(final FcnRcdValue fcn, final Value[] values) {
        this.domain = fcn.domain;
        this.intv = fcn.intv;
        this.values = values;
        this.isNorm = fcn.isNorm;

        if (!isNorm) {
            this.normalize();
        }
//    this.indexTbl = fcn.indexTbl;
    }

    public FcnRcdValue(final ValueVec elems, final Value[] values, final boolean isNorm) {
        this(elems.toArray(), values, isNorm);
    }

    public FcnRcdValue(final ValueVec elems, final Value[] values, final boolean isNorm, final CostModel cm) {
        this(elems, values, isNorm);
        this.cm = cm;
    }

    public FcnRcdValue(final Value[] domain, final Value[] values, final boolean isNorm, final CostModel cm) {
        this(domain, values, isNorm);
        this.cm = cm;
    }

    public FcnRcdValue(final List<Value> vals) {
        this(new IntervalValue(1, vals.size()), vals.toArray(Value[]::new));
    }

    public FcnRcdValue(final Map<Value, Value> pairs) {
        this(pairs, false);
    }

    public FcnRcdValue(final Map<Value, Value> pairs, final boolean isNorm) {
        this(pairs.keySet().toArray(Value[]::new), pairs.values().toArray(Value[]::new), isNorm);
    }

    private static boolean isName(final String name) {
        final int len = name.length();
        boolean hasLetter = false;

        for (int idx = 0; idx < len; idx++) {
            final char ch = name.charAt(idx);
            if (ch == '_') continue;
            if (!Character.isLetterOrDigit(ch)) return false;
            hasLetter = hasLetter || Character.isLetter(ch);
        }

        return hasLetter && (len < 4 || (!name.startsWith("WF_") && !name.startsWith("SF_")));
    }

    public static IValue createFrom(final IValueInputStream vos) throws IOException {
        final int index = vos.getIndex();
        final int len = vos.readNat();
        final int info = vos.readByte();
        final Value res;
        final Value[] rvals = new Value[len];
        if (info == 0) {
            final int low = vos.readInt();
            final int high = vos.readInt();
            for (int i = 0; i < len; i++) {
                rvals[i] = (Value) vos.read();
            }
            final IntervalValue intv = new IntervalValue(low, high);
            res = new FcnRcdValue(intv, rvals);
        } else {
            final Value[] dvals = new Value[len];
            for (int i = 0; i < len; i++) {
                dvals[i] = (Value) vos.read();
                rvals[i] = (Value) vos.read();
            }
            res = new FcnRcdValue(dvals, rvals, (info == 1));
        }
        vos.assign(res, index);
        return res;
    }

    public static IValue createFrom(final ValueInputStream vos, final Map<String, UniqueString> tbl) throws IOException {
        final int index = vos.getIndex();
        final int len = vos.readNat();
        final int info = vos.readByte();
        final Value res;
        final Value[] rvals = new Value[len];
        if (info == 0) {
            final int low = vos.readInt();
            final int high = vos.readInt();
            for (int i = 0; i < len; i++) {
                rvals[i] = (Value) vos.read(tbl);
            }
            final IntervalValue intv = new IntervalValue(low, high);
            res = new FcnRcdValue(intv, rvals);
        } else {
            final Value[] dvals = new Value[len];
            for (int i = 0; i < len; i++) {
                dvals[i] = (Value) vos.read(tbl);
                rvals[i] = (Value) vos.read(tbl);
            }
            res = new FcnRcdValue(dvals, rvals, (info == 1));
        }
        vos.assign(res, index);
        return res;
    }

    @Override
    public final byte getKind() {
        return FCNRCDVALUE;
    }

    @Override
    public final int compareTo(final Object obj) {
        try {

            final FcnRcdValue fcn = obj instanceof Value v ? (FcnRcdValue) v.toFcnRcd() : null;
            if (fcn == null) {
                if (obj instanceof ModelValue mv) {
                    return mv.modelValueCompareTo(this);
                }
                Assert.fail("Attempted to compare the function " + Values.ppr(this.toString()) + " with the value:\n"
                        + Values.ppr(obj.toString()), getSource());
            }

            Objects.requireNonNull(fcn).normalize();

            final int result = this.values.length - fcn.values.length;
            if (result != 0) {
                return result;
            }

            if (this.intv != null) {
                return compareToInterval(fcn);
            } else {
                return compareOtherInterval(fcn);
            }

        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    private int compareOtherInterval(final FcnRcdValue fcn) {
        int result;
        if (fcn.intv != null) {
            for (int i = 0; i < this.domain.length; i++) {
                final Value dElem = this.domain[i];
                if (dElem instanceof IntValue iv) {
                    result = iv.val - (fcn.intv.low + i);

                    if (result != 0) {
                        return result;
                    }
                } else {
                    Assert.fail(
                            "Attempted to compare integer with non-integer\n" + Values.ppr(dElem.toString()) + ".", getSource());
                }
            }
            for (int i = 0; i < this.domain.length; i++) {
                result = this.values[i].compareTo(fcn.values[i]);
                if (result != 0) {
                    return result;
                }
            }
        } else {
            for (int i = 0; i < this.domain.length; i++) {
                result = this.domain[i].compareTo(fcn.domain[i]);
                if (result != 0) {
                    return result;
                }
            }
            for (int i = 0; i < this.domain.length; i++) {
                result = this.values[i].compareTo(fcn.values[i]);
                if (result != 0) {
                    return result;
                }
            }
        }
        return 0;
    }

    private int compareToInterval(final FcnRcdValue fcn) {
        int result;
        if (fcn.intv != null) {
            result = this.intv.low - fcn.intv.low;
            if (result != 0) {
                return result;
            }
            for (int i = 0; i < this.values.length; i++) {
                result = this.values[i].compareTo(fcn.values[i]);
                if (result != 0) {
                    return result;
                }
            }
        } else {
            for (int i = 0; i < fcn.domain.length; i++) {
                final Value dElem = fcn.domain[i];
                if (dElem instanceof IntValue iv) {
                    result = this.intv.low + i - iv.val;
                    if (result != 0) {
                        return result;
                    }
                } else {
                    Assert.fail(
                            "Attempted to compare integer with non-integer:\n" + Values.ppr(dElem.toString()) + ".", getSource());
                }
            }
            for (int i = 0; i < fcn.domain.length; i++) {
                result = this.values[i].compareTo(fcn.values[i]);
                if (result != 0) {
                    return result;
                }
            }
        }
        return 0;
    }

    public final boolean equals(final Object obj) {
        try {

            final FcnRcdValue fcn = obj instanceof Value v ? (FcnRcdValue) v.toFcnRcd() : null;
            if (fcn == null) {
                if (obj instanceof ModelValue mv)
                    return mv.modelValueEquals(this);
                Assert.fail("Attempted to check equality of the function " + Values.ppr(this.toString()) +
                        " with the value:\n" + Values.ppr(obj.toString()), getSource());
            }

            Objects.requireNonNull(fcn).normalize();

            if (this.intv != null) {
                if (fcn.intv != null) {
                    if (!this.intv.equals(fcn.intv)) return false;
                    for (int i = 0; i < this.values.length; i++) {
                        if (!this.values[i].equals(fcn.values[i]))
                            return false;
                    }
                } else {
                    if (fcn.domain.length != this.intv.size()) return false;
                    for (int i = 0; i < fcn.domain.length; i++) {
                        final Value dElem = fcn.domain[i];
                        if (dElem instanceof IntValue iv) {
                            if (iv.val != (this.intv.low + i)) {
                                return false;
                            }
                        } else {
                            Assert.fail("Attempted to compare an integer with non-integer:\n" +
                                    Values.ppr(dElem.toString()) + ".", getSource());
                        }

                    }
                    for (int i = 0; i < fcn.values.length; i++) {
                        if (!this.values[i].equals(fcn.values[i])) {
                            return false;
                        }
                    }
                }
            } else {
                if (this.values.length != fcn.values.length) return false;
                if (fcn.intv != null) {
                    for (int i = 0; i < this.domain.length; i++) {
                        final Value dElem = this.domain[i];
                        if (dElem instanceof IntValue iv) {
                            if (iv.val != (fcn.intv.low + i)) {
                                return false;
                            }
                        } else {
                            Assert.fail("Attempted to compare an integer with non-integer:\n" +
                                    Values.ppr(dElem.toString()) + ".", getSource());
                        }

                    }
                    for (int i = 0; i < this.values.length; i++) {
                        if (!this.values[i].equals(fcn.values[i])) {
                            return false;
                        }
                    }
                } else {
                    for (int i = 0; i < this.domain.length; i++) {
                        if (!this.domain[i].equals(fcn.domain[i])) {
                            return false;
                        }
                    }
                    for (int i = 0; i < this.values.length; i++) {
                        if (!this.values[i].equals(fcn.values[i])) {
                            return false;
                        }
                    }
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
    public final boolean member(final Value elem) {
        try {
            Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
                    "\nis an element of the function " + Values.ppr(this.toString()), getSource());
            return false;  // make compiler happy
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

    // This implementation has a concurrency bug: https://github.com/tlaplus/tlaplus/issues/439

    @Override
    public final Value apply(final Value arg, final int control) {
        try {
            final Value result = this.select(arg);
            if (result == null) {
                Assert.fail("Attempted to apply function:\n" + Values.ppr(this.toString()) +
                        "\nto argument " + Values.ppr(arg.toString()) + ", which is" +
                        " not in the domain of the function.", getSource());
            }
            return result;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /* This one does not seem to be needed anymore.  */
    @Override
    public final Value apply(final Value[] args, final int control) {
        try {
            return this.apply(new TupleValue(args), EvalControl.Clear);
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

            if (this.intv != null) {
                // domain is represented as an integer interval:
                if (arg instanceof IntValue iv) {
                    final int idx = iv.val;
                    if ((idx >= this.intv.low) && (idx <= this.intv.high)) {
                        return this.values[idx - this.intv.low];
                    }
                } else {
                    Assert.fail("Attempted to apply function with integer domain to" +
                            " the non-integer argument " + Values.ppr(arg.toString()), getSource());
                }

                return null;
            } else {
                return selectBinarySearch(arg);
            }
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    final Value selectLinearSearch(final Value arg) {
        // domain is represented as an array of values:
        final int len = this.domain.length;
        for (int i = 0; i < len; i++) {
            if (this.domain[i].equals(arg)) {
                return this.values[i];
            }
        }
        return null;
    }

    final Value selectBinarySearch(final Value arg) {
        // The value 32 has been determined empirically (see FcnRcdBenachmark).
        // In older versions of TLC this the threshold was 10.
        if (this.isNorm && this.domain.length >= LINEAR_SEARCH_THRESHOLD) {
            // domain is represented as an array of values:
            // iff normalized, use binary search to speedup lookups.
            final int idx = Arrays.binarySearch(this.domain, arg, Value::compareTo);
            if (idx >= 0 && this.domain[idx].equals(arg)) {
                // Check equality and cmp here to not introduce subtle bugs should Value#compareTo
                // behaving slightly differently for some types. Linear search and the old,
                // hash-based lookup use/used Value#equals.
                return this.values[idx];
            }
            return null;
        } else {
            return selectLinearSearch(arg);
        }
    }

    @Override
    public final Value takeExcept(final ValueExcept ex) {
        try {

            if (ex.idx >= ex.path.length) return ex.value;

            final int flen = this.values.length;
            final Value[] newValues = new Value[flen];
            System.arraycopy(this.values, 0, newValues, 0, flen);
            final Value arg = ex.path[ex.idx];

            if (this.intv != null) {
                // domain is represented as an integer interval:
                if (arg instanceof IntValue iv) {
                    final int idx = iv.val;
                    if ((idx >= this.intv.low) && (idx <= this.intv.high)) {
                        final int vidx = idx - this.intv.low;
                        ex.idx++;
                        newValues[vidx] = this.values[vidx].takeExcept(ex);
                    }
                    return new FcnRcdValue(this.intv, newValues);
                }
            } else {
                // domain is represented as an array of values:
                for (int i = 0; i < flen; i++) {
                    if (arg.equals(this.domain[i])) {
                        ex.idx++;
                        newValues[i] = newValues[i].takeExcept(ex);
                        Value[] newDomain = this.domain;
                        if (!this.isNorm) {
                            newDomain = new Value[flen];
                            System.arraycopy(this.domain, 0, newDomain, 0, flen);
                        }
                        return new FcnRcdValue(newDomain, newValues, this.isNorm);
                    }
                }
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
    public final Value takeExcept(final ValueExcept[] exs) {
        try {
            Value res = this;
            for (final ValueExcept ex : exs) {
                res = res.takeExcept(ex);
            }
            return res;
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
            if (this.intv != null) {
                return this.intv;
            }

            return new SetEnumValue(this.domain, true);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /**
     * Returns the domain of this FunctionRecordValue regardless of its internal
     * representation as either Value[] or IntervalValue as Value[].
     */
    public final Value[] getDomainAsValues() {
        if (this.intv != null) {
            return this.intv.asValues();
        } else {
            return this.domain;
        }
    }

    @Override
    public final int size() {
        try {

            return this.values.length;
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /**
     * {@link #size()} first normalizes, destructively, this instance; for inspections on the size without normalization
     * use this method.
     */
    public int nonNormalizedSize() {
        return values.length;
    }

    @Override
    public final Value toTuple() {
        if (this.intv != null) {
            if (this.intv.low != 1) return null;
            return new TupleValue(this.values);
        }
        final int len = this.values.length;
        final Value[] elems = new Value[len];
        for (int i = 0; i < len; i++) {
            if (!(this.domain[i] instanceof IntValue)) return null;
            final int idx = ((IntValue) this.domain[i]).val;
            if (0 < idx && idx <= len) {
                if (elems[idx - 1] != null) return null;
                elems[idx - 1] = this.values[i];
            } else {
                return null;
            }
        }
        if (coverage) {
            cm.incSecondary(elems.length);
        }
        return new TupleValue(elems, cm);
    }

    @Override
    public final Value toRcd() {
        if (this.domain == null) return null;

        final UniqueString[] vars = new UniqueString[this.domain.length];
        for (int i = 0; i < this.domain.length; i++) {
            if (this.domain[i] instanceof StringValue sv) {
                vars[i] = sv.getVal();
            } else {
                return null;
            }

        }
        if (coverage) {
            cm.incSecondary(this.values.length);
        }
        return new RecordValue(vars, this.values, this.isNormalized(), cm);
    }

    @Override
    public final Value toFcnRcd() {
        return this;
    }

    /* Return true iff this function is in normal form. */
    @Override
    public final boolean isNormalized() {
        return this.isNorm;
    }

    /* This method normalizes (destructively) this function. */
    @Override
    public final Value normalize() {
        try {

            if (!this.isNorm) {
                // Assert.check(this.domain != null)
                final int dlen = this.domain.length;
                for (int i = 1; i < dlen; i++) {
                    final int cmp = this.domain[0].compareTo(this.domain[i]);
                    if (cmp == 0) {
                        Assert.fail("The value\n" + this.domain[i] +
                                "\noccurs multiple times in the function domain.", getSource());
                    } else if (cmp > 0) {
                        Value tv = this.domain[0];
                        this.domain[0] = this.domain[i];
                        this.domain[i] = tv;
                        tv = this.values[0];
                        this.values[0] = this.values[i];
                        this.values[i] = tv;
                    }
                }
                for (int i = 2; i < dlen; i++) {
                    final Value d = this.domain[i];
                    final Value v = this.values[i];
                    int j = i;
                    int cmp;
                    while ((cmp = d.compareTo(this.domain[j - 1])) < 0) {
                        this.domain[j] = this.domain[j - 1];
                        this.values[j] = this.values[j - 1];
                        j--;
                    }
                    if (cmp == 0) {
                        Assert.fail("The value\n" + this.domain[i] +
                                "\noccurs multiple times in the function domain.", getSource());
                    }
                    this.domain[j] = d;
                    this.values[j] = v;
                }
                this.isNorm = true;
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
            if (this.intv == null) {
                for (int i = 0; i < this.values.length; i++) {
                    defined = defined && this.domain[i].isDefined();
                }
            }
            for (final Value value : this.values) {
                defined = defined && value.isDefined();
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
            final Value[] vals = new Value[this.values.length];
            for (int i = 0; i < vals.length; i++) {
                vals[i] = (Value) this.values[i].deepCopy();
            }
            // WRT Arrays.copyOf, see comment in tlc2.value.impl.RecordValue.deepCopy() introduced
            // by git commit 09cfee2d47f98cf9d76b906e1a8cda7cfd06eccc.
            if (this.intv == null) {
                return new FcnRcdValue(Arrays.copyOf(this.domain, this.domain.length), vals, false);
            }
            return new FcnRcdValue(this, vals);
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
            boolean canAssign = ((val instanceof FcnRcdValue) &&
                    this.values.length == ((FcnRcdValue) val).values.length);
            if (!canAssign) return false;
            final FcnRcdValue fcn = (FcnRcdValue) val;
            for (int i = 0; i < this.values.length; i++) {
                canAssign = (canAssign &&
                        this.domain[i].equals(fcn.domain[i]) &&
                        this.values[i].assignable(fcn.values[i]));
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
            vos.writeByte(FCNRCDVALUE);
            final int len = values.length;
            vos.writeNat(len);
            if (intv != null) {
                vos.writeByte((byte) 0);
                vos.writeInt(intv.low);
                vos.writeInt(intv.high);
                for (final Value value : values) {
                    value.write(vos);
                }
            } else {
                vos.writeByte((isNormalized()) ? (byte) 1 : (byte) 2);
                for (int i = 0; i < len; i++) {
                    domain[i].write(vos);
                    values[i].write(vos);
                }
            }
        } else {
            vos.writeByte(DUMMYVALUE);
            vos.writeNat(index);
        }
    }

    /* The fingerprint method.  */
    @Override
    public final long fingerPrint(long fp) {
        try {
            final int flen = this.values.length;
            fp = FP64.Extend(fp, FCNRCDVALUE);
            fp = FP64.Extend(fp, flen);
            if (this.intv == null) {
                for (int i = 0; i < flen; i++) {
                    fp = this.domain[i].fingerPrint(fp);
                    fp = this.values[i].fingerPrint(fp);
                }
            } else {
                for (int i = 0; i < flen; i++) {
                    fp = FP64.Extend(fp, INTVALUE);
                    fp = FP64.Extend(fp, i + this.intv.low);
                    fp = this.values[i].fingerPrint(fp);
                }
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
            final int flen = this.size();
            final Value[] vals = new Value[flen];

            boolean vchanged = false;
            for (int i = 0; i < flen; i++) {
                vals[i] = (Value) this.values[i].permute(perm);
                vchanged = vchanged || (vals[i] != this.values[i]);
            }

            if (this.intv == null) {
                final Value[] dom = new Value[flen];
                boolean dchanged = false;
                for (int i = 0; i < flen; i++) {
                    dom[i] = (Value) this.domain[i].permute(perm);
                    dchanged = dchanged || (dom[i] != this.domain[i]);
                }

                if (dchanged) {
                    return new FcnRcdValue(dom, vals, false);
                } else if (vchanged) {
                    return new FcnRcdValue(this.domain, vals, true);
                }
            } else {
                if (vchanged) {
                    return new FcnRcdValue(this.intv, vals);
                }
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

    private boolean isRcd() {
        if (this.intv != null) return false;
        for (final Value dval : this.domain) {
            final boolean isName = ((dval instanceof StringValue sv) &&
                    isName(sv.val.toString()));
            if (!isName) return false;
        }
        return true;
    }

    private boolean isTuple() {
        if (this.intv != null) {
            return (this.intv.low == 1);
        }
        for (final Value value : this.domain) {
            if (!(value instanceof IntValue)) {
                return false;
            }
        }

        for (int i = 0; i < this.domain.length; i++) {
            if (((IntValue) this.domain[i]).val != (i + 1)) {
                return false;
            }
        }
        return true;
    }

    /* The string representation of the value.  */
    @Override
    public final StringBuilder toString(StringBuilder sb, final int offset, final boolean swallow) {
        try {

            final int len = this.values.length;
            if (len == 0) {
                sb.append("<< >>");
            } else if (this.isRcd()) {
                sb.append("[");
                sb.append(((StringValue) this.domain[0]).val).append(TLAConstants.RECORD_ARROW);
                sb = this.values[0].toString(sb, offset, swallow);

                for (int i = 1; i < len; i++) {
                    sb.append(", ");
                    sb.append(((StringValue) this.domain[i]).val).append(TLAConstants.RECORD_ARROW);
                    sb = this.values[i].toString(sb, offset, swallow);
                }
                sb.append("]");
            } else if (this.isTuple()) {
                // It is actually a sequence:
                sb.append("<<");
                sb = this.values[0].toString(sb, offset, swallow);

                for (int i = 1; i < len; i++) {
                    sb.append(", ");
                    sb = this.values[i].toString(sb, offset, swallow);
                }
                sb.append(">>");
            } else {
                final Value[] domainAsValues = getDomainAsValues();
                sb.append("(");
                sb = domainAsValues[0].toString(sb, offset, swallow);
                sb.append(" :> ");
                sb = this.values[0].toString(sb, offset, swallow);

                for (int i = 1; i < len; i++) {
                    sb.append(" @@ ");
                    sb = domainAsValues[i].toString(sb, offset, swallow);
                    sb.append(" :> ");
                    sb = this.values[i].toString(sb, offset, swallow);
                }
                sb.append(")");
            }
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
        final List<TLCVariable> nestedVars = new ArrayList<>(values.length);
        final Value[] domains = getDomainAsValues();
        for (int i = 0; i < domains.length; i++) {
            final Value dom = domains[i];
            final Value value = values[i];
            final TLCVariable nested = prototype.newInstance(dom.toString(), value, rnd);
            nested.setValue(value.toString());
            nested.setType(value.getTypeString());
            nestedVars.add(nested);
        }
        return nestedVars;
    }
}
