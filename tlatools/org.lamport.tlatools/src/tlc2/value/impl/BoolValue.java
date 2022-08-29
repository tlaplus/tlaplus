// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:01:16 PST by lamport
//      modified on Fri Aug 10 15:07:07 PDT 2001 by yuanyu

package tlc2.value.impl;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.*;
import util.Assert;

import java.io.IOException;

public class BoolValue extends Value implements IBoolValue {
    public static final BoolValue ValFalse = new BoolValue(false);
    /* Value constants. */
    public static final BoolValue ValTrue = new BoolValue(true);
    private static final long serialVersionUID = -782332311372582825L;
    public final boolean val;   // the boolean

    /* Constructor */
    public BoolValue(final boolean b) {
        this.val = b;
    }

    @Override
    public final boolean getVal() {
        return val;
    }

    @Override
    public final byte getKind() {
        return BOOLVALUE;
    }

    @Override
    public final int compareTo(final Object obj) {
        try {
            if (obj instanceof BoolValue bv) {
                final int x = this.val ? 1 : 0;
                final int y = bv.val ? 1 : 0;
                return x - y;
            } else if (obj instanceof ModelValue mv) {
                return mv.modelValueCompareTo(this);
            } else {
                Assert.fail("Attempted to compare boolean " + Values.ppr(this.toString()) +
                        " with non-boolean:\n" + Values.ppr(obj.toString()), getSource());
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
            if (obj instanceof BoolValue bv) {
                return this.val == bv.val;
            } else if (obj instanceof ModelValue mv) {
                return mv.modelValueEquals(this);
            } else {
                Assert.fail("Attempted to compare equality of boolean " + Values.ppr(this.toString()) +
                        " with non-boolean:\n" + Values.ppr(obj.toString()), getSource());
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
                    "\nis an element of the boolean " + Values.ppr(this.toString()), getSource());
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
        try {
            Assert.fail("Attempted to check if the boolean " + Values.ppr(this.toString()) +
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
                Assert.fail("Attempted to apply EXCEPT construct to the boolean " +
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
                Assert.fail("Attempted to apply EXCEPT construct to the boolean " +
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
            Assert.fail("Attempted to compute the number of elements in the boolean " +
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
            return ((val instanceof BoolValue bv) &&
                    this.val == bv.val);
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
        vos.writeByte(BOOLVALUE);
        vos.writeBoolean(val);
    }

    /* The fingerprint method */
    @Override
    public final long fingerPrint(long fp) {
        try {
            fp = FP64.Extend(fp, BOOLVALUE);
            fp = FP64.Extend(fp, (this.val) ? 't' : 'f');
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
        return this;
    }

    /* The string representation */
    public final StringBuilder toString(final StringBuilder sb, final int offset) {
        return toString(sb, offset, true);
    }

    /* The string representation */
    public final StringBuilder toString(final StringBuilder sb, final int offset, final boolean swallow) {
        try {
            return sb.append((this.val) ? "TRUE" : "FALSE");
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

}
