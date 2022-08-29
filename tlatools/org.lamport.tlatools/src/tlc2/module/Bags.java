// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:18:39 PST by lamport
//      modified on Tue Jan  2 11:40:25 PST 2001 by yuanyu

package tlc2.module;

import tlc2.output.EC;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.impl.TLARegistry;
import tlc2.value.IBoolValue;
import tlc2.value.ValueConstants;
import tlc2.value.Values;
import tlc2.value.impl.*;
import util.Assert;

import java.util.ArrayList;

public class Bags implements ValueConstants {
    public static final long serialVersionUID = 20160822L;

    static {
        // The following entries in TLARegistry each defines a mapping from a TLA+ infix
        // operator to a Java method, e.g. the TLA+ infix operator \\oplus (which is the
        // same as (+) ) is mapped to and thus implemented by the Java method
        // tlc2.module.Bags.BagCup(Value, Value) below.
        Assert.check(TLARegistry.put("BagCup", "\\oplus") == null, EC.TLC_REGISTRY_INIT_ERROR, "BagCup");
        Assert.check(TLARegistry.put("BagDiff", "\\ominus") == null, EC.TLC_REGISTRY_INIT_ERROR, "BagDiff");
        Assert.check(TLARegistry.put("SqSubseteq", "\\sqsubseteq") == null, EC.TLC_REGISTRY_INIT_ERROR, "SqSubseteq");
    }

    public static Value EmptyBag() {
        return FcnRcdValue.EmptyFcn;
    }

    public static IBoolValue IsABag(final Value b) {
        final FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        if (fcn == null) {
            // MAK 02/23/2018 Changed to return ValFalse instead of exception when Value is not a bag.
            return BoolValue.ValFalse;
        }
        final Value[] vals = fcn.values;
        for (final Value val : vals) {
            if (!(val instanceof IntValue iv) || iv.val <= 0) {
                return BoolValue.ValFalse;
            }
        }
        return BoolValue.ValTrue;
    }

    public static IntValue BagCardinality(final Value b) {
        final FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        if (fcn == null) {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"BagCardinality",
                    "a function with a finite domain", Values.ppr(b.toString())});
        }
        int num = 0;
        final Value[] vals = fcn.values;
        for (final Value val : vals) {
            if (val instanceof IntValue iv) {
                final int cnt = iv.val;
                if (cnt > 0) {
                    num += iv.val;
                } else {
                    throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"BagCardinality", "a bag",
                            Values.ppr(b.toString())});
                }
            } else {
                throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"BagCardinality", "a bag",
                        Values.ppr(b.toString())});
            }
        }
        return IntValue.gen(num);
    }

    public static IBoolValue BagIn(final Value e, final Value b) {
        final FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        final Value[] values = fcn.values;
        final Value[] domain = fcn.getDomainAsValues();
        for (int i = 0; i < domain.length; i++) {
            if (e.equals(domain[i])) {
                if (values[i] instanceof IntValue iv) {
                    return (iv.val > 0) ? BoolValue.ValTrue : BoolValue.ValFalse;
                }
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "BagIn", "bag",
                        Values.ppr(b.toString())});
            }
        }
        return BoolValue.ValFalse;
    }

    public static IntValue CopiesIn(final Value e, final Value b) {
        final FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        final Value[] values = fcn.values;
        final Value[] domain = fcn.getDomainAsValues();
        for (int i = 0; i < domain.length; i++) {
            if (e.equals(domain[i])) {
                if (values[i] instanceof IntValue iv) {
                    return iv;
                }
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "CopiesIn", "bag",
                        Values.ppr(b.toString())});
            }
        }
        return IntValue.ValZero;
    }

    public static Value BagCup(final Value b1, final Value b2) {
        final FcnRcdValue fcn1 = (FcnRcdValue) b1.toFcnRcd();
        final FcnRcdValue fcn2 = (FcnRcdValue) b2.toFcnRcd();
        if (!IsABag(fcn1).getVal()) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"first", "(+)", "bag",
                    Values.ppr(b1.toString())});
        }
        if (!IsABag(fcn2).getVal()) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "(+)", "bag",
                    Values.ppr(b2.toString())});
        }
        final Value[] domain1 = fcn1.getDomainAsValues();
        final Value[] values1 = fcn1.values;
        final Value[] domain2 = fcn2.getDomainAsValues();
        final Value[] values2 = fcn2.values;
        final ArrayList<Value> dVec = new ArrayList<>(domain1.length);
        final ArrayList<Value> vVec = new ArrayList<>(domain1.length);
        for (int i = 0; i < domain1.length; i++) {
            dVec.add(domain1[i]);
            vVec.add(values1[i]);
        }
        for (int i = 0; i < domain2.length; i++) {
            boolean found = false;
            for (int j = 0; j < domain1.length; j++) {
                if (domain2[i].equals(domain1[j])) {
                    final int v1 = ((IntValue) values1[j]).val;
                    final int v2 = ((IntValue) values2[i]).val;
                    vVec.set(j, IntValue.gen(v1 + v2));
                    found = true;
                    break;
                }
            }
            if (!found) {
                dVec.add(domain2[i]);
                vVec.add(values2[i]);
            }
        }
        final Value[] domain = new Value[dVec.size()];
        final Value[] values = new Value[dVec.size()];
        for (int i = 0; i < domain.length; i++) {
            domain[i] = dVec.get(i);
            values[i] = vVec.get(i);
        }
        return new FcnRcdValue(domain, values, false);
    }

    public static Value BagDiff(final Value b1, final Value b2) {
        final FcnRcdValue fcn1 = (FcnRcdValue) b1.toFcnRcd();
        final FcnRcdValue fcn2 = (FcnRcdValue) b2.toFcnRcd();
        if (fcn1 == null) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"first", "(-)", "bag",
                    Values.ppr(b1.toString())});
        }
        if (fcn2 == null) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "(-)", "bag",
                    Values.ppr(b2.toString())});
        }
        final Value[] domain1 = fcn1.getDomainAsValues();
        final Value[] values1 = fcn1.values;
        final Value[] domain2 = fcn2.getDomainAsValues();
        final Value[] values2 = fcn2.values;
        final ArrayList<Value> dVec = new ArrayList<>(domain1.length);
        final ArrayList<Value> vVec = new ArrayList<>(domain1.length);
        for (int i = 0; i < domain1.length; i++) {
            int v1 = ((IntValue) values1[i]).val;
            for (int j = 0; j < domain2.length; j++) {
                if (domain1[i].equals(domain2[j])) {
                    final int v2 = ((IntValue) values2[j]).val;
                    v1 -= v2;
                    break;
                }
            }
            if (v1 > 0) {
                dVec.add(domain1[i]);
                vVec.add(IntValue.gen(v1));
            }
        }
        final Value[] domain = new Value[dVec.size()];
        final Value[] values = new Value[vVec.size()];
        for (int i = 0; i < domain.length; i++) {
            domain[i] = dVec.get(i);
            values[i] = vVec.get(i);
        }
        return new FcnRcdValue(domain, values, fcn1.isNormalized());
    }

    public static Value BagUnion(final Value s) {
        final SetEnumValue s1 = (SetEnumValue) s.toSetEnum();
        if (s1 == null) {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"BagUnion",
                    "a finite enumerable set", Values.ppr(s.toString())});
        }
        // MAK 02/20/2018:
        // Need to normalize s in cases where it is an unnormalized set of identical
        // bags, such as h == [ i \in 1..3 |-> 1 ] and BagUnion({h, h}). In other
        // words, let b be a bag, BagUnion({b,b}) = b and not b (+) b. This
        // unfortunately degrades performance due to sorting s1's elements.
        s1.normalize();

        final ValueVec elems = s1.elems;
        final int sz = elems.size();
        if (sz == 0) {
            return FcnRcdValue.EmptyFcn;
        }
        if (sz == 1) {
            return elems.get(0);
        }
        final ValueVec dVec = new ValueVec();
        final ValueVec vVec = new ValueVec();
        FcnRcdValue fcn = (FcnRcdValue) elems.get(0).toFcnRcd();
        if (fcn == null) {
            throw new EvalException(EC.TLC_MODULE_BAG_UNION1, Values.ppr(s.toString()));
        }
        Value[] domain = fcn.getDomainAsValues();
        Value[] values = fcn.values;
        for (int i = 0; i < domain.length; i++) {
            dVec.add(domain[i]);
            vVec.add(values[i]);
        }
        for (int i = 1; i < sz; i++) {
            fcn = (FcnRcdValue) elems.get(i).toFcnRcd();
            if (fcn == null) {

                throw new EvalException(EC.TLC_MODULE_BAG_UNION1, Values.ppr(s.toString()));
            }
            domain = fcn.getDomainAsValues();
            values = fcn.values;
            for (int j = 0; j < domain.length; j++) {
                boolean found = false;
                for (int k = 0; k < dVec.size(); k++) {
                    if (domain[j].equals(dVec.get(k))) {
                        final int v1 = ((IntValue) vVec.get(k)).val;
                        final int v2 = ((IntValue) values[j]).val;
                        vVec.setElementAt(IntValue.gen(v1 + v2), k);
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    dVec.add(domain[j]);
                    vVec.add(values[j]);
                }
            }
        }
        final Value[] dom = new Value[dVec.size()];
        final Value[] vals = new Value[vVec.size()];
        for (int i = 0; i < dom.length; i++) {
            dom[i] = dVec.get(i);
            vals[i] = vVec.get(i);
        }
        return new FcnRcdValue(dom, vals, false);
    }

    public static IBoolValue SqSubseteq(final Value b1, final Value b2) {
        final FcnRcdValue fcn1 = (FcnRcdValue) b1.toFcnRcd();
        final FcnRcdValue fcn2 = (FcnRcdValue) b2.toFcnRcd();
        if (fcn1 == null) {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"\\sqsubseteq",
                    "a function with a finite domain", Values.ppr(b1.toString())});
        }
        if (fcn2 == null) {

            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"\\sqsubseteq",
                    "a function with a finite domain", Values.ppr(b2.toString())});
        }
        final Value[] domain1 = fcn1.getDomainAsValues();
        final Value[] values1 = fcn1.values;
        final Value[] domain2 = fcn2.getDomainAsValues();
        final Value[] values2 = fcn2.values;
        for (int i = 0; i < domain1.length; i++) {
            int v1 = ((IntValue) values1[i]).val;
            for (int j = 0; j < domain2.length; j++) {
                if (domain1[i].equals(domain2[j])) {
                    final int v2 = ((IntValue) values2[j]).val;
                    v1 -= v2;
                    break;
                }
            }
            if (v1 > 0)
                return BoolValue.ValFalse;
        }
        return BoolValue.ValTrue;
    }

    public static Value BagOfAll(final Value f, final Value b) {
        if (!(f instanceof final Applicable ff)) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[]{"first", "BagOfAll", "operator",
                    Values.ppr(f.toString())});
        }
        final FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        if (fcn == null) {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[]{"second", "BagOfAll",
                    "function with a finite domain", Values.ppr(b.toString())});
        }
        final ValueVec dVec = new ValueVec();
        final ValueVec vVec = new ValueVec();
        final Value[] domain = fcn.getDomainAsValues();
        final Value[] values = fcn.values;
        final Value[] args = new Value[1];
        for (int i = 0; i < domain.length; i++) {
            args[0] = domain[i];
            final Value val = ff.apply(args, EvalControl.Clear);
            boolean found = false;
            for (int j = 0; j < dVec.size(); j++) {
                if (val.equals(dVec.get(j))) {
                    final int v1 = ((IntValue) vVec.get(j)).val;
                    final int v2 = ((IntValue) values[i]).val;
                    vVec.setElementAt(IntValue.gen(v1 + v2), j);
                    found = true;
                    break;
                }
            }
            if (!found) {
                dVec.add(val);
                vVec.add(values[i]);
            }
        }
        final Value[] dom = new Value[dVec.size()];
        final Value[] vals = new Value[vVec.size()];
        for (int i = 0; i < dom.length; i++) {
            dom[i] = dVec.get(i);
            vals[i] = vVec.get(i);
        }
        return new FcnRcdValue(dom, vals, false);
    }

    /******
     // For now, we do not override SubBag. So, We are using the TLA+ definition.
     public static Value SubBag(Value b) {
     FcnRcdValue fcn = b.toFcnRcd();
     if (fcn == null) {
     String msg = "Applying SubBag to the following value, which is\n" +
     "not a function with a finite domain:\n" + Value.ppr(b.toString());
     throw new EvalException(msg);
     }
     throw new EvalException("SubBag is not implemented.");
     }
     ******/

    public static Value BagToSet(final Value b) {
        final FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        if (fcn == null) {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"BagToSet",
                    "a function with a finite domain", Values.ppr(b.toString())});
        }
        return fcn.getDomain();
    }

    public static Value SetToBag(final Value b) {
        final SetEnumValue s1 = (SetEnumValue) b.toSetEnum();
        if (s1 == null) {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"BagToSet",
                    "a function with a finite domain", Values.ppr(b.toString())});
        }
        // The following `if' added by LL on 5 Mar 2012 to correct a bug found by Tom Rodeheffer,
        // in which SetToBag creates a function with multiple copies of the elements in its
        // domain, and this causes BagToSet to report an error.
        if (!s1.isNormalized()) {
            s1.normalize();
        }
        final ValueVec elems = s1.elems;
        final Value[] domain = new Value[elems.size()];
        final Value[] values = new Value[elems.size()];
        for (int i = 0; i < elems.size(); i++) {
            domain[i] = elems.get(i);
            values[i] = IntValue.ValOne;
        }
        return new FcnRcdValue(domain, values, s1.isNormalized());
    }

}
