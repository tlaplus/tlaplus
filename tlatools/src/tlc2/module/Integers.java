// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at  9:52:48 PST by lamport
//      modified on Thu Jan  4 21:06:47 PST 2001 by yuanyu

package tlc2.module;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.tool.TLARegistry;
import tlc2.value.BoolValue;
import tlc2.value.IntValue;
import tlc2.value.IntervalValue;
import tlc2.value.ModelValue;
import tlc2.value.UserObj;
import tlc2.value.UserValue;
import tlc2.value.Value;
import tlc2.value.ValueConstants;

public class Integers extends UserObj implements ValueConstants
{

    static
    {
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

    private static Value SetInt = new UserValue(new Integers());

    public static Value Int()
    {
        return SetInt;
    }

    public static Value Nat()
    {
        return Naturals.Nat();
    }

    public static IntValue Plus(IntValue x, IntValue y)
    {
        return Naturals.Plus(x, y);
    }

    public static IntValue Minus(IntValue x, IntValue y)
    {
        return Naturals.Minus(x, y);
    }

    public static IntValue Times(IntValue x, IntValue y)
    {
        return Naturals.Times(x, y);
    }

    public static BoolValue LT(Value x, Value y)
    {
        if (!(x instanceof IntValue))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[] { "first", "<", "integer",
                    Value.ppr(x.toString()) });
        }
        if (!(y instanceof IntValue))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[] { "second", "<", "integer",
                    Value.ppr(y.toString()) });
        }

        return (((IntValue) x).val < ((IntValue) y).val) ? ValTrue : ValFalse;
    }

    public static BoolValue LE(Value x, Value y)
    {
        if (!(x instanceof IntValue))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[] { "first", "<=", "integer",
                    Value.ppr(x.toString()) });
        }
        if (!(y instanceof IntValue))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[] { "second", "<=", "integer",
                    Value.ppr(x.toString()) });
        }

        return (((IntValue) x).val <= ((IntValue) y).val) ? ValTrue : ValFalse;
    }

    public static BoolValue GT(Value x, Value y)
    {
        if (!(x instanceof IntValue))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[] { "first", ">", "integer",
                    Value.ppr(x.toString()) });
        }
        if (!(y instanceof IntValue))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[] { "second", ">", "integer",
                    Value.ppr(x.toString()) });
        }

        return (((IntValue) x).val > ((IntValue) y).val) ? ValTrue : ValFalse;
    }

    public static BoolValue GEQ(Value x, Value y)
    {
        if (!(x instanceof IntValue))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[] { "first", ">=", "integer",
                    Value.ppr(x.toString()) });
        }
        if (!(y instanceof IntValue))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[] { "second", ">=", "integer",
                    Value.ppr(x.toString()) });
        }

        return (((IntValue) x).val >= ((IntValue) y).val) ? ValTrue : ValFalse;
    }

    public static IntervalValue DotDot(IntValue x, IntValue y)
    {
        return new IntervalValue(x.val, y.val);
    }

    public static IntValue Neg(IntValue x)
    {
        int n = x.val;
        if (n == -2147483648)
        {
            throw new EvalException(EC.TLC_MODULE_OVERFLOW, "--2147483648");
        }
        return IntValue.gen(0 - n);
    }

    public static IntValue Divide(IntValue x, IntValue y)
    {
        if (y.val == 0)
        {
            throw new EvalException(EC.TLC_MODULE_DIVISION_BY_ZERO);
        }
        if (x.val == -2147483648 && y.val == -1)
        {
            throw new EvalException(EC.TLC_MODULE_OVERFLOW, "-2147483648 \\div -1");
        }
        int n1 = x.val;
        int n2 = y.val;
        int q = n1 / n2;
        if ((((n1 < 0) && (n2 > 0)) || ((n1 > 0) && (n2 < 0))) && (q * y.val != x.val))
        {
            q--;
        }
        return IntValue.gen(q);
    }

    public static IntValue Mod(IntValue x, IntValue y)
    {
        if (y.val <= 0)
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "%", "positive number",
                    y.toString() });
        }
        int r = x.val % y.val;
        return IntValue.gen(r < 0 ? (r + y.val) : r);
    }

    public static IntValue Expt(IntValue x, IntValue y)
    {
        if (y.val < 0)
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "^", "natural number",
                    y.toString() });
        }
        if (y.val == 0)
        {
            if (x.val == 0)
            {
                throw new EvalException(EC.TLC_MODULE_NULL_POWER_NULL);
            }
            return ValOne;
        }
        long res = x.val;
        for (int i = 1; i < y.val; i++)
        {
            res *= x.val;
            if (res < -2147483648 || res > 2147483647)
            {

                throw new EvalException(EC.TLC_MODULE_OVERFLOW, x.val + "^" + y.val);
            }
        }
        return IntValue.gen((int) res);
    }

    public final int compareTo(Value val)
    {
        if (val instanceof UserValue)
        {
            if (((UserValue) val).userObj instanceof Integers)
            {
                return 0;
            }
            if (((UserValue) val).userObj instanceof Naturals)
            {
                return 1;
            }
        }
        if (val instanceof ModelValue)
            return 1;
        throw new EvalException(EC.TLC_MODULE_COMPARE_VALUE, new String[] { "Int", Value.ppr(val.toString()) });
    }

    public final boolean member(Value val)
    {
        if (val instanceof IntValue)
            return true;
        if (val instanceof ModelValue)
        {
            return ((ModelValue) val).modelValueMember(this);
        }
        throw new EvalException(EC.TLC_MODULE_CHECK_MEMBER_OF, new String[] { Value.ppr(val.toString()), "Int" });
    }

    public final boolean isFinite()
    {
        return false;
    }

    public final StringBuffer toString(StringBuffer sb, int offset)
    {
        return sb.append("Int");
    }
}
