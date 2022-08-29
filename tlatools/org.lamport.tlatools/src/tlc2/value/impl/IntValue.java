// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:08:05 PST by lamport
//      modified on Fri Aug 10 15:07:30 PDT 2001 by yuanyu

package tlc2.value.impl;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;

import java.io.IOException;
import java.util.Objects;

public class IntValue extends Value {
    private static final long serialVersionUID = 3127167023658570028L;

    private static final IntValue[] cache;
    public static final IntValue ValNegOne;
    public static final IntValue ValOne;
    public static final IntValue ValZero;

    static {
        cache = new IntValue[10];
        for (int i = 0; i < cache.length; i++) {
            cache[i] = new IntValue(i);
        }

        // cache must be set first
        ValNegOne = gen(-1);
        ValOne = gen(1);
        ValZero = gen(0);
    }

    public final int val;

    private IntValue(final int i) {
        this.val = i;
    }

    public static int nbits(int tmp) {
        int nb = 0;
        while (tmp != 0 && tmp != -1) {
            nb++;
            tmp >>= 1;
        }
        return nb + 1;
    }

    public static IntValue gen(final int i) {
        if (i >= 0 && i < cache.length) {
            return cache[i];
        }
        return new IntValue(i);
    }

    @Override
    public final byte getKind() {
        return INTVALUE;
    }

    // the number of bits needed to encode the value of this int
    public final int nbits() {
        try {
            return nbits(this.val);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public final int compareTo(final Object obj) {
        try {
            if (obj instanceof IntValue iv) {
                return Integer.compare(this.val, iv.val);
            } else if (obj instanceof ModelValue mv) {
                return mv.modelValueCompareTo(this);
            } else {
                Assert.fail("Attempted to compare integer " + Values.ppr(this.toString()) +
                        " with non-integer:\n" + Values.ppr(obj.toString()), getSource());

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

    public final boolean equals(final Object obj) {
        try {
            if (obj instanceof IntValue iv) {
                return this.val == iv.val;
            } else if (obj instanceof ModelValue mv) {
                return mv.modelValueEquals(this);
            } else {
                Assert.fail("Attempted to check equality of integer " + Values.ppr(this.toString()) +
                        " with non-integer:\n" + Values.ppr(Objects.requireNonNullElse(obj, "null").toString()), getSource());
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
    public final boolean member(final Value elem) {
        try {
            Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
                    "\nis an element of the integer " + Values.ppr(this.toString()), getSource());
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
        try {
            Assert.fail("Attempted to check if the integer " + Values.ppr(this.toString()) +
                    " is a finite set.", getSource());
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
    public final Value takeExcept(final ValueExcept ex) {
        try {
            if (ex.idx < ex.path.length) {
                Assert.fail("Attempted to appy EXCEPT construct to the integer " +
                        Values.ppr(this.toString()) + ".", getSource());
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
                Assert.fail("Attempted to apply EXCEPT construct to the integer " +
                        Values.ppr(this.toString()) + ".", getSource());
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
            Assert.fail("Attempted to compute the number of elements in the integer " +
                    Values.ppr(this.toString()) + ".", getSource());
            return 0;   // make compiler happy
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public boolean mutates() {
        // finalized after construction.
        return false;
    }

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
        return true;
    }

    @Override
    public final IValue deepCopy() {
        return this;
    }

    @Override
    public final boolean assignable(final Value val) {
        try {
            return ((val instanceof IntValue iv) &&
                    this.val == iv.val);
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
        vos.writeByte(INTVALUE);
        vos.writeInt(val);
    }

    /* The fingerprint methods */
    @Override
    public final long fingerPrint(final long fp) {
        try {
            return FP64.Extend(FP64.Extend(fp, INTVALUE), this.val);
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
        return this;
    }

    /* The string representation. */
    @Override
    public final StringBuilder toString(final StringBuilder sb, final int offset, final boolean ignored) {
        try {
            return sb.append(this.val);
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

}
