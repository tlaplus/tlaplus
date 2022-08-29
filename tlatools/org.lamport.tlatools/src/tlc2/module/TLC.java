// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:19:45 PST by lamport
//      modified on Tue Aug  7 10:46:55 PDT 2001 by yuanyu

package tlc2.module;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.impl.TLARegistry;
import tlc2.value.IBoolValue;
import tlc2.value.ValueConstants;
import tlc2.value.Values;
import tlc2.value.impl.*;
import util.Assert;
import util.ToolIO;

import java.io.IOException;
import java.io.Writer;

public class TLC implements ValueConstants {

    public static final long serialVersionUID = 20160822L;

    public static Writer OUTPUT;

    static {
        // The following two entries in TLARegistry define a mapping from a TLA+ infix
        // operator to a Java method, e.g. the TLA+ infix operator "@@" is mapped to CombineFcn and
        // thus implemented by the Java method tlc2.module.TLC.CombineFcn(Value, Value)
        // below.
        Assert.check(TLARegistry.put("MakeFcn", ":>") == null, EC.TLC_REGISTRY_INIT_ERROR, "MakeFcn");
        Assert.check(TLARegistry.put("CombineFcn", "@@") == null, EC.TLC_REGISTRY_INIT_ERROR, "CombineFcn");
    }

    /**
     * Prints to standard error the string (v1 + "  " + v2), and
     * returns the value v2.
     * <p>
     * Modified on 22 June 2011 by LL to call deepNormalize() on the values before
     * printing.  This fixes the same bug that caused PrintT({"a", "a"}) to print
     * {"a", "a"} instead of {"a"}.  For safety, the values are copied before normalizing,
     * thought that's probably not necessary.
     */
    public static Value Print(final Value v1, final Value v2) {
        final Value v1c = (Value) v1.deepCopy();
        final Value v2c = (Value) v2.deepCopy();
        v1c.deepNormalize();
        v2c.deepNormalize();
        if (OUTPUT == null) {
            ToolIO.out.println(Values.ppr(v1c.toStringUnchecked()) + "  " + Values.ppr(v2c.toStringUnchecked()));
        } else {
            try {
                OUTPUT.write(Values.ppr(v1c.toStringUnchecked()) + "  " + Values.ppr(v2c.toStringUnchecked()) + "\n");
            } catch (final IOException e) {
                MP.printError(EC.GENERAL, e);
            }
        }
        return v2;
    }

    /**
     * Prints to standard error the string v1. Always returns TRUE.
     * <p>
     * Modified on 22 June 2011 by LL.  See comment on the Print method
     */
    public static Value PrintT(final Value v1) {
        final Value v1c = (Value) v1.deepCopy();
        v1c.deepNormalize();
        if (OUTPUT == null) {
            final String ppr = Values.ppr(v1c.toStringUnchecked());
            ToolIO.out.println(ppr);
        } else {
            try {
                OUTPUT.write(Values.ppr(v1c.toStringUnchecked("\n")));
            } catch (final IOException e) {
                MP.printError(EC.GENERAL, e);
            }
        }
        return BoolValue.ValTrue;
    }

    /* Returns the string value of the string representation of v. */
    public static Value ToString(final Value v) {
        return new StringValue(v.toStringUnchecked());
    }

    /**
     * Returns true if the value of v1 is true. Otherwise, throws
     * an exception with v2 as the error message.
     */
    public static Value Assert(final Value v1, final Value v2) {
        if ((v1 instanceof IBoolValue) && ((BoolValue) v1).val) {
            return v1;
        }
        throw new EvalException(EC.TLC_VALUE_ASSERT_FAILED, Values.ppr(v2.toString()));
    }

    /**
     * The current wall clock time.  Note that it is not declared as final.
     * So, TLC will not treat it as a constant.
     */
    public static Value JavaTime() {
        // MAK 11/30/2021:
        // Prevent wall-clock time from going backward for a while longer by converting
        // milliseconds to seconds (since epoch), which "gains" ~10 bits before the Java
        // type int overflows. This change should be safe, assuming specs do not rely on
        // sub-second time resolution -- TLC!JavaTime never guaranteed time to increment
        // between two states.
        //TODO: Switch to 64 bit integers (long) to prevent year 2038 problem.
        final int t = (int) (System.currentTimeMillis() / 1000L);
        // Zero MSB to prevent time going negative when 2^31 overflows
        // (there is no unsigned variant of IntValue).  Instead, time
        // will go backwards, which satisfies the definition
        //   CHOOSE n : n \in Nat  in  TLC!JavaTime.
        return IntValue.gen(t & 0x7FFFFFFF);
    }

    public static Value MakeFcn(final Value d, final Value e) {
        final Value[] dom = new Value[1];
        final Value[] vals = new Value[1];
        dom[0] = d;
        vals[0] = e;
        return new FcnRcdValue(dom, vals, true);
    }

    /**
     * f @@ g == [x \in (DOMAIN f) \cup (DOMAIN g) |->
     * IF x \in DOMAIN f THEN f[x] ELSE g[x]]
     */
    public static Value CombineFcn(final Value f1, final Value f2) {
        final FcnRcdValue fcn1 = (FcnRcdValue) f1.toFcnRcd();
        final FcnRcdValue fcn2 = (FcnRcdValue) f2.toFcnRcd();
        if (fcn1 == null) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"first", "@@", "function",
                    Values.ppr(f1.toString())});
        }
        if (fcn2 == null) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "@@", "function",
                    Values.ppr(f2.toString())});
        }
        final ValueVec dom = new ValueVec();
        final ValueVec vals = new ValueVec();
        final Value[] vals1 = fcn1.values;
        final Value[] vals2 = fcn2.values;

        final Value[] dom1 = fcn1.domain;
        if (dom1 == null) {
            final IntervalValue intv1 = fcn1.intv;
            for (int i = intv1.low; i <= intv1.high; i++) {
                dom.add(IntValue.gen(i));
                vals.add(vals1[i - intv1.low]);
            }
        } else {
            for (int i = 0; i < dom1.length; i++) {
                dom.add(dom1[i]);
                vals.add(vals1[i]);
            }
        }

        final int len1 = dom.size();
        final Value[] dom2 = fcn2.domain;
        if (dom2 == null) {
            final IntervalValue intv2 = fcn2.intv;
            for (int i = intv2.low; i <= intv2.high; i++) {
                final Value val = IntValue.gen(i);
                boolean found = false;
                for (int j = 0; j < len1; j++) {
                    if (val.equals(dom.get(j))) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    dom.add(val);
                    vals.add(vals2[i - intv2.low]);
                }
            }
        } else {
            for (int i = 0; i < dom2.length; i++) {
                final Value val = dom2[i];
                boolean found = false;
                for (int j = 0; j < len1; j++) {
                    if (val.equals(dom.get(j))) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    dom.add(val);
                    vals.add(vals2[i]);
                }
            }
        }

        final Value[] domain = new Value[dom.size()];
        final Value[] values = new Value[dom.size()];
        for (int i = 0; i < domain.length; i++) {
            domain[i] = dom.get(i);
            values[i] = vals.get(i);
        }
        return new FcnRcdValue(domain, values, false);
    }

    public static Value SortSeq(final Value s, final Value cmp) {
        final TupleValue seq = (TupleValue) s.toTuple();
        if (seq == null) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"first", "SortSeq", "natural number",
                    Values.ppr(s.toString())});
        }
        if (!(cmp instanceof final Applicable fcmp)) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "SortSeq", "function",
                    Values.ppr(cmp.toString())});
        }
        final Value[] elems = seq.elems;
        final int len = elems.length;
        if (len == 0)
            return seq;
        final Value[] args = new Value[2];
        final Value[] newElems = new Value[len];
        newElems[0] = elems[0];
        for (int i = 1; i < len; i++) {
            int j = i;
            args[0] = elems[i];
            args[1] = newElems[j - 1];
            while (compare(fcmp, args)) {
                newElems[j] = newElems[j - 1];
                j--;
                if (j == 0)
                    break;
                args[1] = newElems[j - 1];
            }
            newElems[j] = args[0];
        }
        return new TupleValue(newElems);
    }

    private static boolean compare(final Applicable fcmp, final Value[] args) {
        final Value res = fcmp.apply(args, EvalControl.Clear);
        if (res instanceof IBoolValue) {
            return ((BoolValue) res).val;
        }
        throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "SortSeq", "boolean function",
                Values.ppr(res.toString())});
    }

    // Returns a set of size n! where n = |s|.
    public static Value Permutations(final Value s) {
        final SetEnumValue s1 = (SetEnumValue) s.toSetEnum();
        if (s1 == null) {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"Permutations",
                    "a finite set", Values.ppr(s.toString())});
        }
        s1.normalize();
        final ValueVec elems = s1.elems;
        final int len = elems.size();
        if (len == 0) {
            final Value[] elems1 = {FcnRcdValue.EmptyFcn};
            return new SetEnumValue(elems1, true);
        }

        int factorial = 1;
        final Value[] domain = new Value[len];
        final int[] idxArray = new int[len];
        final boolean[] inUse = new boolean[len];
        for (int i = 0; i < len; i++) {
            domain[i] = elems.get(i);
            idxArray[i] = i;
            inUse[i] = true;
            factorial = factorial * (i + 1);
        }

        final ValueVec fcns = new ValueVec(factorial);
        _done:
        while (true) {
            final Value[] vals = new Value[len];
            for (int i = 0; i < len; i++) {
                vals[i] = domain[idxArray[i]];
            }
            fcns.add(new FcnRcdValue(domain, vals, true));
            int i;
            for (i = len - 1; i >= 0; i--) {
                boolean found = false;
                for (int j = idxArray[i] + 1; j < len; j++) {
                    if (!inUse[j]) {
                        inUse[j] = true;
                        inUse[idxArray[i]] = false;
                        idxArray[i] = j;
                        found = true;
                        break;
                    }
                }
                if (found) {
                    break;
                }
                if (i == 0) {
                    break _done;
                }
                inUse[idxArray[i]] = false;
            }
            for (int j = i + 1; j < len; j++) {
                for (int k = 0; k < len; k++) {
                    if (!inUse[k]) {
                        inUse[k] = true;
                        idxArray[j] = k;
                        break;
                    }
                }
            }
        }
        return new SetEnumValue(fcns, false);
    }

    public static Value RandomElement(final Value val) {
        switch (val.getKind()) {
            case SETOFFCNSVALUE -> {
                final SetOfFcnsValue sfv = (SetOfFcnsValue) val;
                sfv.normalize();
                final SetEnumValue domSet = (SetEnumValue) sfv.domain.toSetEnum();
                if (domSet == null) {
                    throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"RandomElement",
                            "a finite set", Values.ppr(val.toString())});
                }
                domSet.normalize();
                final ValueVec elems = domSet.elems;
                final Value[] dom = new Value[elems.size()];
                final Value[] vals = new Value[elems.size()];
                for (int i = 0; i < dom.length; i++) {
                    dom[i] = elems.get(i);
                    vals[i] = RandomElement(sfv.range);
                }
                return new FcnRcdValue(dom, vals, true);
            }
            case SETOFRCDSVALUE -> {
                final SetOfRcdsValue srv = (SetOfRcdsValue) val;
                srv.normalize();
                final Value[] vals = new Value[srv.names.length];
                for (int i = 0; i < vals.length; i++) {
                    vals[i] = RandomElement(srv.values[i]);
                }
                return new RecordValue(srv.names, vals, true);
            }
            case SETOFTUPLESVALUE -> {
                final SetOfTuplesValue stv = (SetOfTuplesValue) val;
                stv.normalize();
                final Value[] vals = new Value[stv.sets.length];
                for (int i = 0; i < vals.length; i++) {
                    vals[i] = RandomElement(stv.sets[i]);
                }
                return new TupleValue(vals);
            }
            case INTERVALVALUE -> {
                final IntervalValue iv = (IntervalValue) val;
                return iv.randomElement();
            }
            default -> {
                final SetEnumValue enumVal = (SetEnumValue) val.toSetEnum();
                if (enumVal == null) {
                    throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"RandomElement",
                            "a finite set", Values.ppr(val.toString())});
                }
                return enumVal.randomElement();
            }
        }
    }

    public static Value Any() {
        return AnySet.ANY();
    }

    /**
     * Implements TLCEval, which causes TLC to eagerly evaluate the
     * value.  Useful for preventing inefficiency caused by lazy evaluation
     * defeating efforts at common subexpression elimination.
     *
     * @param val
     * @return
     */

}
