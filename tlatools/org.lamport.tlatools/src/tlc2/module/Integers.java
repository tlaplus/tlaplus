// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at  9:52:48 PST by lamport
//      modified on Thu Jan  4 21:06:47 PST 2001 by yuanyu

package tlc2.module;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.tool.impl.TLARegistry;
import tlc2.value.IBoolValue;
import tlc2.value.ValueConstants;
import tlc2.value.Values;
import tlc2.value.impl.*;

public class Integers extends UserObj implements ValueConstants {
    public static final long serialVersionUID = 20160822L;
    private static final Value SetInt = new UserValue(new Integers());

    static {
        // The following entries in TLARegistry each define a mapping from a TLA+ infix
        // operator to a Java method, e.g. the TLA+ infix operator "+" is mapped to and
        // thus implemented by the Java method tlc2.module.Integers.Plus(IntValue,
        // IntValue) below.
        //TODO Why does tlc2.module.Naturals define identical mappings?
        TLARegistry.put("Plus", "+");
        TLARegistry.put("Minus", "-");
        TLARegistry.put("Times", "*");
        TLARegistry.put("LT", "<");
        TLARegistry.put("LE", "\\leq");
        TLARegistry.put("GT", ">");
        TLARegistry.put("GEQ", "\\geq");
        TLARegistry.put("DotDot", "..");
        TLARegistry.put("Neg", "-.");
        TLARegistry.put("Divide", "\\div");
        TLARegistry.put("Mod", "%");
        TLARegistry.put("Expt", "^");
    }

    public static Value Int() {
        return SetInt;
    }

    public static Value Nat() {
        return Naturals.Nat();
    }

    public static IntValue Plus(final IntValue x, final IntValue y) {
        return Naturals.Plus(x, y);
    }

    public static IntValue Minus(final IntValue x, final IntValue y) {
        return Naturals.Minus(x, y);
    }

    public static IntValue Times(final IntValue x, final IntValue y) {
        return Naturals.Times(x, y);
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

    public static BoolValue GT(final Value x, final Value y) {
        if (x instanceof IntValue xIV) {
            if (y instanceof IntValue yIV) {
                return (xIV.val > yIV.val) ? BoolValue.ValTrue : BoolValue.ValFalse;
            } else {
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
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[]{"second", ">=", "integer",
                        Values.ppr(y.toString())});
            }
        } else {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[]{"first", ">=", "integer",
                    Values.ppr(x.toString())});
        }
    }

    public static IntervalValue DotDot(final IntValue x, final IntValue y) {
        return new IntervalValue(x.val, y.val);
    }

    public static IntValue Neg(final IntValue x) {
        final int n = x.val;
        if (n == -2147483648) {
            throw new EvalException(EC.TLC_MODULE_OVERFLOW, "--2147483648");
        }
        return IntValue.gen(0 - n);
    }

    public static IntValue Divide(final IntValue x, final IntValue y) {
        if (y.val == 0) {
            throw new EvalException(EC.TLC_MODULE_DIVISION_BY_ZERO);
        }
        if (x.val == -2147483648 && y.val == -1) {
            throw new EvalException(EC.TLC_MODULE_OVERFLOW, "-2147483648 \\div -1");
        }
        final int n1 = x.val;
        final int n2 = y.val;
        int q = n1 / n2;
        if ((((n1 < 0) && (n2 > 0)) || ((n1 > 0) && (n2 < 0))) && (q * y.val != x.val)) {
            q--;
        }
        return IntValue.gen(q);
    }

    public static IntValue Mod(final IntValue x, final IntValue y) {
        if (y.val <= 0) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "%", "positive number",
                    y.toString()});
        }
        final int r = x.val % y.val;
        return IntValue.gen(r < 0 ? (r + y.val) : r);
    }

    public static IntValue Expt(final IntValue x, final IntValue y) {
        if (y.val < 0) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "^", "natural number",
                    y.toString()});
        }
        if (y.val == 0) {
            if (x.val == 0) {
                throw new EvalException(EC.TLC_MODULE_NULL_POWER_NULL);
            }
            return IntValue.ValOne;
        }
        long res = x.val;
        for (int i = 1; i < y.val; i++) {
            res *= x.val;
            if (res < -2147483648 || res > 2147483647) {

                throw new EvalException(EC.TLC_MODULE_OVERFLOW, x.val + "^" + y.val);
            }
        }
        return IntValue.gen((int) res);
    }

    @Override
    public final int compareTo(final Value val) {
        if (val instanceof UserValue uv) {
            if (uv.userObj instanceof Integers) {
                return 0;
            }
            if (uv.userObj instanceof Naturals) {
                return 1;
            }
        }
        if (val instanceof ModelValue)
            return 1;
        throw new EvalException(EC.TLC_MODULE_COMPARE_VALUE, new String[]{"Int", Values.ppr(val.toString())});
    }

    @Override
    public final boolean member(final Value val) {
        if (val instanceof IntValue)
            return true;
        if (val instanceof ModelValue mv) {
            return mv.modelValueMember(this);
        }
        throw new EvalException(EC.TLC_MODULE_CHECK_MEMBER_OF, new String[]{Values.ppr(val.toString()), "Int"});
    }

    @Override
    public final boolean isFinite() {
        return false;
    }

    @Override
    public final StringBuilder toString(final StringBuilder sb, final int offset, final boolean swallow) {
        return sb.append("Int");
    }
}
