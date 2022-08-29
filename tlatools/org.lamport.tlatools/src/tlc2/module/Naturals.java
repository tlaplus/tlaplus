// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at  9:52:47 PST by lamport
//      modified on Tue Jan  2 21:36:16 PST 2001 by yuanyu

package tlc2.module;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.tool.impl.TLARegistry;
import tlc2.value.IBoolValue;
import tlc2.value.ValueConstants;
import tlc2.value.Values;
import tlc2.value.impl.*;

public class Naturals extends UserObj implements ValueConstants {
    public static final long serialVersionUID = 20160822L;
    private static final Value SetNat = new UserValue(new Naturals());

    static {
        // The following entries in TLARegistry each define a mapping from a TLA+ infix
        // operator to a Java method, e.g. the TLA+ infix operator "+" is mapped to and
        // thus implemented by the Java method tlc2.module.Naturals.Plus(IntValue,
        // IntValue) below.
        //TODO Why does tlc2.module.Integers define identical mappings?
        TLARegistry.put("Plus", "+");
        TLARegistry.put("Minus", "-");
        TLARegistry.put("Times", "*");
        TLARegistry.put("LT", "<");
        TLARegistry.put("LE", "\\leq");
        TLARegistry.put("GT", ">");
        TLARegistry.put("GEQ", "\\geq");
        TLARegistry.put("DotDot", "..");
        TLARegistry.put("Divide", "\\div");
        TLARegistry.put("Mod", "%");
        TLARegistry.put("Expt", "^");
    }

    public static Value Nat() {
        return SetNat;
    }

    public static IntValue Plus(final IntValue x, final IntValue y) {
        final int n1 = x.val;
        final int n2 = y.val;
        final int res = n1 + n2;
        if ((n1 < 0) == (n2 < 0) && (n2 < 0) != (res < 0)) {
            throw new EvalException(EC.TLC_MODULE_OVERFLOW, n1 + "+" + n2);
        }
        return IntValue.gen(res);
    }

    public static IntValue Minus(final IntValue x, final IntValue y) {
        final int n1 = x.val;
        final int n2 = y.val;
        final int res = n1 - n2;
        if ((n1 < 0) != (n2 < 0) && (n1 < 0) != (res < 0)) {
            throw new EvalException(EC.TLC_MODULE_OVERFLOW, n1 + "-" + n2);
        }
        return IntValue.gen(res);
    }

    public static IntValue Times(final IntValue x, final IntValue y) {
        final int n1 = x.val;
        final int n2 = y.val;
        /* The following line was originally
         *      long res = n1 * n2
         * which was wrong because in Java, * for ints  multiplication mod
         * 2^n for some n.  I'm not sure the new code is correct, but it's
         * at least better.  Modified by LL on 10 Jul 2009.
         */
        final long res = ((long) n1) * ((long) n2);
        if (-2147483648 > res || res > 2147483647) {
            throw new EvalException(EC.TLC_MODULE_OVERFLOW, n1 + "*" + n2);
        }
        return IntValue.gen((int) res);
    }

    public static IBoolValue LT(final Value x, final Value y) {
        if (x instanceof IntValue xIV) {
            if (y instanceof IntValue yIV) {
                return (xIV.val < yIV.val) ? BoolValue.ValTrue : BoolValue.ValFalse;
            } else {
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[]{"second", "<", "integer",
                        Values.ppr(y.toString())});
            }
        } else {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[]{"first", "<", "integer",
                    Values.ppr(x.toString())});
        }
    }

    public static IBoolValue LE(final Value x, final Value y) {
        if (x instanceof IntValue xIV) {
            if (y instanceof IntValue yIV) {
                return (xIV.val <= yIV.val) ? BoolValue.ValTrue : BoolValue.ValFalse;
            } else {
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[]{"second", "<=", "integer",
                        Values.ppr(y.toString())});
            }
        } else {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[]{"first", "<=", "integer",
                    Values.ppr(x.toString())});
        }

    }

    public static IBoolValue GT(final Value x, final Value y) {
        if (x instanceof IntValue xIV) {
            if (y instanceof IntValue yIV) {
                return (xIV.val > yIV.val) ? BoolValue.ValTrue : BoolValue.ValFalse;
            } else {
                // On 21 May 2012 LL corrected following call, which was reporting the first argument.
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[]{"second", ">", "integer",
                        Values.ppr(y.toString())});
            }
        } else {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[]{"first", ">", "integer",
                    Values.ppr(x.toString())});
        }
    }

    public static IBoolValue GEQ(final Value x, final Value y) {
        if (x instanceof IntValue xIV) {
            if (y instanceof IntValue yIV) {
                return (xIV.val >= yIV.val) ? BoolValue.ValTrue : BoolValue.ValFalse;
            } else {
                // On 21 May 2012 LL corrected following call, which was reporting the first argument.
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[]{"second", ">", "integer",
                        Values.ppr(y.toString())});
            }
        } else {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[]{"first", ">", "integer",
                    Values.ppr(x.toString())});
        }


    }

    public static IntervalValue DotDot(final IntValue x, final IntValue y) {
        return new IntervalValue(x.val, y.val);
    }

    public static IntValue Divide(final IntValue x, final IntValue y) {
        final int n1 = x.val;
        final int n2 = y.val;
        if (n2 == 0) {
            throw new EvalException(EC.TLC_MODULE_DIVISION_BY_ZERO);
        }
        int q = n1 / n2;
        if ((q < 0) && (q * n2 != n1))
            q--;
        return IntValue.gen(q);
    }

    public static IntValue Mod(final IntValue x, final IntValue y) {
        final int n1 = x.val;
        final int n2 = y.val;
        if (n2 <= 0) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "%", "positive number",
                    String.valueOf(n2)});
        }
        final int r = n1 % n2;
        return IntValue.gen(r < 0 ? (r + n2) : r);
    }

    public static IntValue Expt(final IntValue x, final IntValue y) {
        final int n1 = x.val;
        final int n2 = y.val;
        if (n2 < 0) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "^", "natural number",
                    String.valueOf(n2)});
        }
        if (n2 == 0) {
            if (n1 == 0) {
                throw new EvalException(EC.TLC_MODULE_NULL_POWER_NULL);
            }
            return IntValue.ValOne;
        }
        long res = n1;
        for (int i = 1; i < n2; i++) {
            res *= n1;
            if (res < -2147483648 || res > 2147483647) {
                throw new EvalException(EC.TLC_MODULE_OVERFLOW, n1 + "^" + n2);
            }
        }
        return IntValue.gen((int) res);
    }

    @Override
    public final int compareTo(final Value val) {
        if (val instanceof UserValue uv) {
            if (uv.userObj instanceof Naturals) {
                return 0;
            }
            if (uv.userObj instanceof Integers) {
                return -1;
            }
        }
        if (val instanceof ModelValue)
            return 1;
        throw new EvalException(EC.TLC_MODULE_COMPARE_VALUE, new String[]{"Nat", Values.ppr(val.toString())});
    }

    @Override
    public final boolean member(final Value val) {
        if (val instanceof IntValue iv)
            return iv.val >= 0;
        if (val instanceof ModelValue mv)
            return mv.modelValueMember(this);

        throw new EvalException(EC.TLC_MODULE_CHECK_MEMBER_OF, new String[]{Values.ppr(val.toString()), "Nat"});
    }

    @Override
    public final boolean isFinite() {
        return false;
    }

    @Override
    public final StringBuilder toString(final StringBuilder sb, final int offset, final boolean swallow) {
        return sb.append("Nat");
    }
}
