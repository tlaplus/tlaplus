// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:19:41 PST by lamport
//      modified on Fri Aug 10 15:06:37 PDT 2001 by yuanyu

package tlc2.value.impl;

import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.util.FP64;
import tlc2.value.*;
import util.Assert;
import util.UniqueString;

import java.io.IOException;
import java.util.Map;
import java.util.Random;

public class StringValue extends Value {
    private static final long serialVersionUID = 2662360691785009553L;
    public final UniqueString val;

    /* Constructor */
    public StringValue(final String str) {
        // SZ 11.04.2009: changed the access method to equivalent
        this.val = UniqueString.uniqueStringOf(str);
    }

    public StringValue(final UniqueString var) {
        this.val = var;
    }

    public StringValue(final UniqueString var, final CostModel cm) {
        this(var);
        this.cm = cm;
    }

    public static IValue createFrom(final IValueInputStream vos) throws IOException {
        final UniqueString str = UniqueString.read(vos.getInputStream());
        final IValue res = new StringValue(str);
        final int index = vos.getIndex();
        vos.assign(res, index);
        return res;
    }

    public static IValue createFrom(final IValueInputStream vos, final Map<String, UniqueString> tbl) throws IOException {
        final UniqueString str = UniqueString.read(vos.getInputStream(), tbl);
        final IValue res = new StringValue(str);
        final int index = vos.getIndex();
        vos.assign(res, index);
        return res;
    }

    @Override
    public final byte getKind() {
        return STRINGVALUE;
    }

    public final UniqueString getVal() {
        return this.val;
    }

    @Override
    public final int compareTo(final Object obj) {
        try {
            if (obj instanceof StringValue sv) {
                return this.val.compareTo(sv.val);
            } else if (obj instanceof ModelValue mv) {
                return mv.modelValueCompareTo(this);
            } else {
                Assert.fail("Attempted to compare string " + Values.ppr(this.toString()) +
                        " with non-string:\n" + Values.ppr(obj.toString()), getSource());
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
            if (obj instanceof StringValue sv) {
                return this.val.equals(sv.getVal());
            } else if (obj instanceof ModelValue mv) {
                return mv.modelValueEquals(this);
            } else {
                Assert.fail("Attempted to check equality of string " + Values.ppr(this.toString()) +
                        " with non-string:\n" + Values.ppr(obj.toString()), getSource());
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
                    "\nis an element of the string " + Values.ppr(this.toString()), getSource());
            return false;     // make compiler happy
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
            Assert.fail("Attempted to check if the string " + Values.ppr(this.toString()) +
                    " is a finite set.", getSource());
            return false;     // make compiler happy
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
                Assert.fail("Attempted to apply EXCEPT construct to the string " +
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
                Assert.fail("Attempted to apply EXCEPT construct to the string " +
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
            Assert.fail("Attempted to compute the number of elements in the string " +
                    Values.ppr(this.toString()) + ".", getSource());
            return 0;       // make compiler happy
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
    public final Value normalize() { /*SKIP*/
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
            return ((val instanceof StringValue) &&
                    this.equals(val));
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    public final int length() {
        try {
            return this.val.length();
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
        final int index = vos.put(this);
        if (index == -1) {
            vos.writeByte(STRINGVALUE);
            val.write(vos.getOutputStream());
        } else {
            vos.writeByte(DUMMYVALUE);
            vos.writeNat(index);
        }
    }

    /* The fingerprint method */
    @Override
    public final long fingerPrint(long fp) {
        try {
            fp = FP64.Extend(fp, STRINGVALUE);
            fp = FP64.Extend(fp, this.val.length());
            fp = FP64.Extend(fp, this.val.toString());
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

    /*************************************************************************
     * toString() modified 23 Aug 2007 by LL to call PrintVersion so strings  *
     * with special characters are printed properly.                          *
     *************************************************************************/
    final String PrintVersion(final String str) {
        try {
            final StringBuilder buf = new StringBuilder(str.length());
            for (int i = 0; i < str.length(); i++) {
                switch (str.charAt(i)) {
                    case '\"' -> buf.append("\\\"");
                    case '\\' -> buf.append("\\\\");
                    case '\t' -> buf.append("\\t");
                    case '\n' -> buf.append("\\n");
                    case '\f' -> buf.append("\\f");
                    case '\r' -> buf.append("\\r");
                    default -> buf.append(str.charAt(i));
                } // switch
            }// for
            return buf.toString();
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    @Override
    public TLCVariable toTLCVariable(final TLCVariable variable, final Random rnd) {
        final TLCVariable stringVar = super.toTLCVariable(variable, rnd);
        // Replace the quoted string from super.toTLCVariable(..) with an unquoted one.
        // In the variable view of the debugger, we don't want quotes.
        stringVar.setValue(toUnquotedString());
        return stringVar;
    }

    /* The string representation of the value. */
    @Override
    public StringBuilder toString(final StringBuilder sb, final int offset, final boolean swallow) {
        try {
            return sb.append("\"").append(PrintVersion(this.val.toString())).append("\"");
        } catch (final RuntimeException | OutOfMemoryError e) {
            if (hasSource()) {
                throw FingerprintException.getNewHead(this, e);
            } else {
                throw e;
            }
        }
    }

    /* Same as toString. */
    @Override
    public final String toUnquotedString() {
        return PrintVersion(this.val.toString());
    }
}
