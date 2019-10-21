// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:18:39 PST by lamport
//      modified on Tue Jan  2 11:40:25 PST 2001 by yuanyu

package tlc2.module;

import tlc2.output.EC;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.impl.TLARegistry;
import tlc2.util.Vect;
import tlc2.value.IBoolValue;
import tlc2.value.ValueConstants;
import tlc2.value.Values;
import tlc2.value.impl.Applicable;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueVec;
import util.Assert;

public class Bags implements ValueConstants
{
	public static final long serialVersionUID = 20160822L;

    static
    {
		// The following entries in TLARegistry each defines a mapping from a TLA+ infix
		// operator to a Java method, e.g. the TLA+ infix operator \\oplus (which is the
		// same as (+) ) is mapped to and thus implemented by the Java method
		// tlc2.module.Bags.BagCup(Value, Value) below.
        Assert.check(TLARegistry.put("BagCup", "\\oplus") == null, EC.TLC_REGISTRY_INIT_ERROR, "BagCup");
        Assert.check(TLARegistry.put("BagDiff", "\\ominus") == null, EC.TLC_REGISTRY_INIT_ERROR, "BagDiff");
        Assert.check(TLARegistry.put("SqSubseteq", "\\sqsubseteq") == null, EC.TLC_REGISTRY_INIT_ERROR, "SqSubseteq");
    }

    public static Value EmptyBag()
    {
        return FcnRcdValue.EmptyFcn;
    }

    public static IBoolValue IsABag(final Value b)
    {
        final FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        if (fcn == null)
        {
        	// MAK 02/23/2018 Changed to return ValFalse instead of exception when Value is not a bag.
            //throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[] { "IsBag",
            //        "a function with a finite domain", Value.ppr(b.toString()) });
        	return BoolValue.ValFalse;
        }
        final Value[] vals = fcn.values;
        for (int i = 0; i < vals.length; i++)
        {
            if (!(vals[i] instanceof IntValue) || ((IntValue) vals[i]).val <= 0)
            {
                return BoolValue.ValFalse;
            }
        }
        return BoolValue.ValTrue;
    }

    public static IntValue BagCardinality(Value b)
    {
        FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        if (fcn == null)
        {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[] { "BagCardinality",
                    "a function with a finite domain", Values.ppr(b.toString()) });
        }
        int num = 0;
        Value[] vals = fcn.values;
        for (int i = 0; i < vals.length; i++)
        {
            if (vals[i] instanceof IntValue)
            {
                int cnt = ((IntValue) vals[i]).val;
                if (cnt > 0)
                {
                    num += ((IntValue) vals[i]).val;
                } else
                {
                    throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[] { "BagCardinality", "a bag",
                            Values.ppr(b.toString()) });
                }
            } else
            {
            	throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[] { "BagCardinality", "a bag",
                        Values.ppr(b.toString()) });
            }
        }
        return IntValue.gen(num);
    }

    public static IBoolValue BagIn(final Value e, final Value b)
    {
        final FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        final Value[] values = fcn.values;
        final Value[] domain = fcn.getDomainAsValues();
        for (int i = 0; i < domain.length; i++)
        {
            if (e.equals(domain[i]))
            {
                if (values[i] instanceof IntValue)
                {
                    return (((IntValue) values[i]).val > 0) ? BoolValue.ValTrue : BoolValue.ValFalse;
                }
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "BagIn", "bag",
                        Values.ppr(b.toString()) });
            }
        }
        return BoolValue.ValFalse;
    }

    public static IntValue CopiesIn(final Value e, final Value b)
    {
        final FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        final Value[] values = fcn.values;
        final Value[] domain = fcn.getDomainAsValues();
        for (int i = 0; i < domain.length; i++)
        {
            if (e.equals(domain[i]))
            {
                if (values[i] instanceof IntValue)
                {
                    return (IntValue) values[i];
                }
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "CopiesIn", "bag",
                        Values.ppr(b.toString()) });
            }
        }
        return IntValue.ValZero;
    }

    public static Value BagCup(Value b1, Value b2)
    {
        FcnRcdValue fcn1 = (FcnRcdValue) b1.toFcnRcd();
        FcnRcdValue fcn2 = (FcnRcdValue) b2.toFcnRcd();
        if (!IsABag(fcn1).getVal())
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "first", "(+)", "bag",
                    Values.ppr(b1.toString()) });
        }
        if (!IsABag(fcn2).getVal())
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "(+)", "bag",
                    Values.ppr(b2.toString()) });
        }
        Value[] domain1 = fcn1.getDomainAsValues();
        Value[] values1 = fcn1.values;
        Value[] domain2 = fcn2.getDomainAsValues();
        Value[] values2 = fcn2.values;
        Vect<Value> dVec = new Vect<>(domain1.length);
        Vect<Value> vVec = new Vect<>(domain1.length);
        for (int i = 0; i < domain1.length; i++)
        {
            dVec.addElement(domain1[i]);
            vVec.addElement(values1[i]);
        }
        for (int i = 0; i < domain2.length; i++)
        {
            boolean found = false;
            for (int j = 0; j < domain1.length; j++)
            {
                if (domain2[i].equals(domain1[j]))
                {
                    int v1 = ((IntValue) values1[j]).val;
                    int v2 = ((IntValue) values2[i]).val;
                    vVec.setElementAt(IntValue.gen(v1 + v2), j);
                    found = true;
                    break;
                }
            }
            if (!found)
            {
                dVec.addElement(domain2[i]);
                vVec.addElement(values2[i]);
            }
        }
        Value[] domain = new Value[dVec.size()];
        Value[] values = new Value[dVec.size()];
        for (int i = 0; i < domain.length; i++)
        {
            domain[i] = dVec.elementAt(i);
            values[i] = vVec.elementAt(i);
        }
        return new FcnRcdValue(domain, values, false);
    }

    public static Value BagDiff(Value b1, Value b2)
    {
        FcnRcdValue fcn1 = (FcnRcdValue) b1.toFcnRcd();
        FcnRcdValue fcn2 = (FcnRcdValue) b2.toFcnRcd();
        if (fcn1 == null)
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "first", "(-)", "bag",
                    Values.ppr(b1.toString()) });
        }
        if (fcn2 == null)
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "(-)", "bag",
                    Values.ppr(b2.toString()) });
        }
        Value[] domain1 = fcn1.getDomainAsValues();
        Value[] values1 = fcn1.values;
        Value[] domain2 = fcn2.getDomainAsValues();
        Value[] values2 = fcn2.values;
        Vect<Value> dVec = new Vect<>(domain1.length);
        Vect<Value> vVec = new Vect<>(domain1.length);
        for (int i = 0; i < domain1.length; i++)
        {
            int v1 = ((IntValue) values1[i]).val;
            for (int j = 0; j < domain2.length; j++)
            {
                if (domain1[i].equals(domain2[j]))
                {
                    int v2 = ((IntValue) values2[j]).val;
                    v1 -= v2;
                    break;
                }
            }
            if (v1 > 0)
            {
                dVec.addElement(domain1[i]);
                vVec.addElement(IntValue.gen(v1));
            }
        }
        Value[] domain = new Value[dVec.size()];
        Value[] values = new Value[vVec.size()];
        for (int i = 0; i < domain.length; i++)
        {
            domain[i] = dVec.elementAt(i);
            values[i] = vVec.elementAt(i);
        }
        return new FcnRcdValue(domain, values, fcn1.isNormalized());
    }

    public static Value BagUnion(final Value s)
    {
        final SetEnumValue s1 = (SetEnumValue) s.toSetEnum();
        if (s1 == null)
        {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[] { "BagUnion",
                    "a finite enumerable set", Values.ppr(s.toString()) });
        }
        // MAK 02/20/2018:
        // Need to normalize s in cases where it is an unnormalized set of identical
        // bags, such as h == [ i \in 1..3 |-> 1 ] and BagUnion({h, h}). In other
        // words, let b be a bag, BagUnion({b,b}) = b and not b (+) b. This
        // unfortunately degrades performance due to sorting s1's elements.
        s1.normalize();

        ValueVec elems = s1.elems;
        int sz = elems.size();
        if (sz == 0) {
        	return FcnRcdValue.EmptyFcn;
        }
        if (sz == 1) {
        	return elems.elementAt(0);
        }
        ValueVec dVec = new ValueVec();
        ValueVec vVec = new ValueVec();
        FcnRcdValue fcn = (FcnRcdValue) elems.elementAt(0).toFcnRcd();
        if (fcn == null)
        {
            throw new EvalException(EC.TLC_MODULE_BAG_UNION1, Values.ppr(s.toString()));
        }
        Value[] domain = fcn.getDomainAsValues();
        Value[] values = fcn.values;
        for (int i = 0; i < domain.length; i++)
        {
            dVec.addElement(domain[i]);
            vVec.addElement(values[i]);
        }
        for (int i = 1; i < sz; i++)
        {
            fcn = (FcnRcdValue) elems.elementAt(i).toFcnRcd();
            if (fcn == null)
            {

                throw new EvalException(EC.TLC_MODULE_BAG_UNION1, Values.ppr(s.toString()));
            }
            domain = fcn.getDomainAsValues();
            values = fcn.values;
            for (int j = 0; j < domain.length; j++)
            {
                boolean found = false;
                for (int k = 0; k < dVec.size(); k++)
                {
                    if (domain[j].equals(dVec.elementAt(k)))
                    {
                        int v1 = ((IntValue) vVec.elementAt(k)).val;
                        int v2 = ((IntValue) values[j]).val;
                        vVec.setElementAt(IntValue.gen(v1 + v2), k);
                        found = true;
                        break;
                    }
                }
                if (!found)
                {
                    dVec.addElement(domain[j]);
                    vVec.addElement(values[j]);
                }
            }
        }
        Value[] dom = new Value[dVec.size()];
        Value[] vals = new Value[vVec.size()];
        for (int i = 0; i < dom.length; i++)
        {
            dom[i] = dVec.elementAt(i);
            vals[i] = vVec.elementAt(i);
        }
        return new FcnRcdValue(dom, vals, false);
    }

    public static IBoolValue SqSubseteq(Value b1, Value b2)
    {
        FcnRcdValue fcn1 = (FcnRcdValue) b1.toFcnRcd();
        FcnRcdValue fcn2 = (FcnRcdValue) b2.toFcnRcd();
        if (fcn1 == null)
        {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[] { "\\sqsubseteq",
                    "a function with a finite domain", Values.ppr(b1.toString()) });
        }
        if (fcn2 == null)
        {

            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[] { "\\sqsubseteq",
                    "a function with a finite domain", Values.ppr(b2.toString()) });
        }
        Value[] domain1 = fcn1.getDomainAsValues();
        Value[] values1 = fcn1.values;
        Value[] domain2 = fcn2.getDomainAsValues();
        Value[] values2 = fcn2.values;
        for (int i = 0; i < domain1.length; i++)
        {
            int v1 = ((IntValue) values1[i]).val;
            for (int j = 0; j < domain2.length; j++)
            {
                if (domain1[i].equals(domain2[j]))
                {
                    int v2 = ((IntValue) values2[j]).val;
                    v1 -= v2;
                    break;
                }
            }
            if (v1 > 0)
                return BoolValue.ValFalse;
        }
        return BoolValue.ValTrue;
    }

    public static Value BagOfAll(Value f, Value b)
    {
        if (!(f instanceof Applicable))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR_AN, new String[] { "first", "BagOfAll", "operator",
                    Values.ppr(f.toString()) });
        }
        FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        if (fcn == null)
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "BagOfAll",
                    "function with a finite domain", Values.ppr(b.toString()) });
        }
        Applicable ff = (Applicable) f;
        ValueVec dVec = new ValueVec();
        ValueVec vVec = new ValueVec();
        Value[] domain = fcn.getDomainAsValues();
        Value[] values = fcn.values;
        Value[] args = new Value[1];
        for (int i = 0; i < domain.length; i++)
        {
            args[0] = domain[i];
            Value val = ff.apply(args, EvalControl.Clear);
            boolean found = false;
            for (int j = 0; j < dVec.size(); j++)
            {
                if (val.equals(dVec.elementAt(j)))
                {
                    int v1 = ((IntValue) vVec.elementAt(j)).val;
                    int v2 = ((IntValue) values[i]).val;
                    vVec.setElementAt(IntValue.gen(v1 + v2), j);
                    found = true;
                    break;
                }
            }
            if (!found)
            {
                dVec.addElement(val);
                vVec.addElement(values[i]);
            }
        }
        Value[] dom = new Value[dVec.size()];
        Value[] vals = new Value[vVec.size()];
        for (int i = 0; i < dom.length; i++)
        {
            dom[i] = dVec.elementAt(i);
            vals[i] = vVec.elementAt(i);
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

    public static Value BagToSet(Value b)
    {
        FcnRcdValue fcn = (FcnRcdValue) b.toFcnRcd();
        if (fcn == null)
        {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[] { "BagToSet",
                    "a function with a finite domain", Values.ppr(b.toString()) });
        }
        return fcn.getDomain();
    }

    public static Value SetToBag(Value b)
    {
        SetEnumValue s1 = (SetEnumValue) b.toSetEnum();
        if (s1 == null)
        {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[] { "BagToSet",
                    "a function with a finite domain", Values.ppr(b.toString()) });
        }
        // The following `if' added by LL on 5 Mar 2012 to correct a bug found by Tom Rodeheffer,
        // in which SetToBag creates a function with multiple copies of the elements in its
        // domain, and this causes BagToSet to report an error.
        if (!s1.isNormalized()) {
        	s1.normalize();
        }
        ValueVec elems = s1.elems;
        Value[] domain = new Value[elems.size()];
        Value[] values = new Value[elems.size()];
        for (int i = 0; i < elems.size(); i++)
        {
            domain[i] = elems.elementAt(i);
            values[i] = IntValue.ValOne;
        }
        return new FcnRcdValue(domain, values, s1.isNormalized());
    }

}
