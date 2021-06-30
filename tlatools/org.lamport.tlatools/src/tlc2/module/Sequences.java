// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at  9:53:48 PST by lamport
//      modified on Fri Jun 29 23:58:36 PDT 2001 by yuanyu

package tlc2.module;

import tlc2.output.EC;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.impl.TLARegistry;
import tlc2.value.IBoolValue;
import tlc2.value.ValueConstants;
import tlc2.value.Values;
import tlc2.value.impl.Applicable;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.OpLambdaValue;
import tlc2.value.impl.OpRcdValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.UserObj;
import tlc2.value.impl.UserValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueVec;
import util.Assert;
import util.UniqueString;

public class Sequences extends UserObj implements ValueConstants
{
	public static final long serialVersionUID = 20160822L;
	
    private Value range;
    private int size;

    public Sequences(Value range, int size)
    {
        this.range = range;
        this.size = size;
    }

	static
    {
		// This entry in TLARegistry defines a mapping from TLA+' infix
		// operator \o to the Java method tlc2.module.Sequences.Concat(Value, Value)
		// below.
        Assert.check(TLARegistry.put("Concat", "\\o") == null, EC.TLC_REGISTRY_INIT_ERROR, "Concat");
    }

    /* The set of all sequences of value range. */
    public static Value Seq(Value range)
    {
        UserObj obj = new Sequences(range, Integer.MAX_VALUE);
        return new UserValue(obj);
    }

    public static IntValue Len(Value s)
    {
        if (s instanceof StringValue)
        {
            return IntValue.gen(((StringValue) s).length());
        }

        TupleValue seq = (TupleValue) s.toTuple();
        if (seq != null)
        {
            return IntValue.gen(seq.size());
        }
        throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR, new String[] { "Len", "sequence",
                Values.ppr(s.toString()) });
    }

    public static Value Head(Value s)
    {
        TupleValue seq = (TupleValue) s.toTuple();
        if (seq != null)
        {
            if (seq.size() == 0)
            {
                throw new EvalException(EC.TLC_MODULE_APPLY_EMPTY_SEQ, "Head");
            }
            return seq.elems[0];
        }
        throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR, new String[] { "Head", "sequence",
                Values.ppr(s.toString()) });
    }

    public static Value Tail(Value s)
    {
    	// Implementation of Tail(string) by LL on 17 April 2013
    	if (s instanceof StringValue) {
    		String str = ((StringValue) s).val.toString();
    		if (str.equals("")) {
    			throw new EvalException(EC.TLC_MODULE_APPLY_EMPTY_SEQ, "Tail");
    		}
    		return new StringValue(str.substring(1));
    	}
    	
        TupleValue seq = (TupleValue) s.toTuple();
        if (seq != null)
        {
            if (seq.size() == 0)
            {
                throw new EvalException(EC.TLC_MODULE_APPLY_EMPTY_SEQ, "Tail");
            }
            int len = seq.size();
            Value[] vals = new Value[len - 1];
            System.arraycopy(seq.elems, 1, vals, 0, vals.length);
            return new TupleValue(vals);
        }
        throw new EvalException(EC.TLC_MODULE_ONE_ARGUMENT_ERROR, new String[] { "Tail", "sequence",
                Values.ppr(s.toString()) });
    }

    public static Value Cons(Value v, Value s)
    {
        TupleValue seq = (TupleValue) s.toTuple();
        if (seq == null)
        {
            throw new EvalException(EC.TLC_MODULE_EVALUATING, new String[] { "Cons(v, s)", "sequence",
                    Values.ppr(s.toString()) });
        }
        int len = seq.size();
        Value[] values = new Value[len + 1];
        values[0] = v;
        System.arraycopy(seq.elems, 0, values, 1, len);
        return new TupleValue(values);
    }

    public static Value Append(Value s, Value v)
    {
        TupleValue seq = (TupleValue) s.toTuple();
        if (seq == null)
        {
            throw new EvalException(EC.TLC_MODULE_EVALUATING, new String[] { "Append(s, v)", "sequence",
                    Values.ppr(s.toString()) });
        }
        int len = seq.size();
        Value[] values = new Value[len + 1];
        System.arraycopy(seq.elems, 0, values, 0, len);
        values[len] = v;
        return new TupleValue(values);
    }

    public static Value Concat(Value s1, Value s2)
    {
        if (s1 instanceof StringValue)
        {
            if (!(s2 instanceof StringValue))
            {
                throw new EvalException(EC.TLC_MODULE_EVALUATING, new String[] { "t \\o s", "string",
                        Values.ppr(s2.toString()) });
            }
            UniqueString u1 = ((StringValue) s1).val;
            UniqueString u2 = ((StringValue) s2).val;
            return new StringValue(u1.concat(u2));
        }

        TupleValue seq1 = (TupleValue) s1.toTuple();
        if (seq1 == null)
        {
            throw new EvalException(EC.TLC_MODULE_EVALUATING, new String[] { "s \\o t", "sequence",
                    Values.ppr(s1.toString()) });
        }
        TupleValue seq2 = (TupleValue) s2.toTuple();
        if (seq2 == null)
        {
            throw new EvalException(EC.TLC_MODULE_EVALUATING, new String[] { "t \\o s", "sequence",
                    Values.ppr(s2.toString()) });
        }
        int len1 = seq1.size();
        int len2 = seq2.size();
        if (len1 == 0)
            return seq2;
        if (len2 == 0)
            return seq1;
        Value[] values = new Value[len1 + len2];
        for (int i = 0; i < len1; i++)
        {
            values[i] = seq1.elems[i];
        }
        for (int i = 0; i < len2; i++)
        {
            values[i + len1] = seq2.elems[i];
        }
        return new TupleValue(values);
    }

    /**
     * Returns the index (starting from 1) of the first element to match.
     * If no match, return 0.
     */
    public static Value SelectInSeq(Value s, Value test)
    {
        TupleValue seq = (TupleValue) s.toTuple();
        if (seq == null)
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "first", "SelectInSeq", "sequence",
                    Values.ppr(s.toString()) });
        }
        if (!(test instanceof Applicable))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "SelectInSeq", "function",
                    Values.ppr(test.toString()) });
        }
        int len = seq.size();
        Applicable ftest = (Applicable) test;
        Value[] args = new Value[1];
        for (int i = 0; i < len; i++)
        {
            args[0] = seq.elems[i];
            Value val = ftest.apply(args, EvalControl.Clear);
            if (!(val instanceof IBoolValue))
            {
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "SelectInSeq",
                        "boolean-valued function", Values.ppr(test.toString()) });
            }
            if (((BoolValue) val).val)
                return IntValue.gen(i + 1);
        }
        return IntValue.ValZero;
    }

    /**  Not in the standard interface.
    public static Value Remove(Value s, Value index) {
      TupleValue seq = s.toTuple()
      if (seq != null) {
        if (index instanceof IntValue) {
    int ridx = ((IntValue)index).val;
    int len = seq.size();
    if (ridx > 0 && ridx <= len) {
      Value[] values = new Value[len-1];
      for (int i = 0; i < ridx - 1; i++) {
        values[i] = seq.elems[i];
      }
      for (int j = ridx; j < len; j++) {
        values[j-1] = seq.elems[j];
      }
      return new TupleValue(values);
    }
    else {
      String msg = "The second argument of Remove must be in the " +
        "domain of its first argument:\n" + Value.ppr(s.toString()) +
        "\n, but instead it is\n" + Value.ppr(index.toString());
      throw new EvalException(msg);
    }
        }
        else {
    String msg = "The second argument of Remove must be a natural " +
      "number,\nbut instead it is\n" + Value.ppr(index.toString());
    throw new EvalException(msg);
        }
      }
      String msg = "The first argument of Remove must be " +
        "a sequence, but instead it is\n" + Value.ppr(s.toString());
      throw new EvalException(msg);
    }
    **/

    public static Value SubSeq(Value s, Value m, Value n)
    {
    	// Handling of strings added by LL on 17 Apr 2013
    	boolean isString = false ;
    	String str = null ;
    	TupleValue seq = null ;
    	if (s instanceof StringValue) {
    		str = ((StringValue) s).val.toString();
    		isString = true ;
    	}
    	
    	if (! isString) {
          seq = (TupleValue) s.toTuple();
          if (seq == null)
          {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "first", "SubSeq", "sequence",
                    Values.ppr(s.toString()) });
          }
    	}
    	
        if (!(m instanceof IntValue))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "SubSeq", "natural number",
                    Values.ppr(m.toString()) });
        }
        if (!(n instanceof IntValue))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "third", "SubSeq", "natural number",
                    Values.ppr(n.toString()) });
        }
        int beg = ((IntValue) m).val;
        int end = ((IntValue) n).val;
        if (beg > end) {
        	if (isString) {
        		return new StringValue("") ;
        	} 
        	else {
              return TupleValue.EmptyTuple;
        	}
        }
        
        int len = isString ? str.length() : seq.size();
        int sublen = end - beg + 1;
        if (beg < 1 || beg > len)
        {

            throw new EvalException(EC.TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN, new String[] { "second", "SubSeq", "first",
                    Values.ppr(s.toString()), Values.ppr(m.toString()) });
        }
        if (end < 1 || end > len)
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN, new String[] { "third", "SubSeq", "first",
                    Values.ppr(s.toString()), Values.ppr(n.toString()) });
        }
        
        if (isString) {
        	return new StringValue(str.substring(beg-1,end));
        }
        Value[] elems = new Value[sublen];
        for (int i = 0; i < sublen; i++)
        {
            elems[i] = seq.elems[beg + i - 1];
        }
        return new TupleValue(elems);
    }

    public static Value SelectSeq(Value s, Value test)
    {
        TupleValue seq = (TupleValue) s.toTuple();
        if (seq == null)
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "first", "SelectSeq", "sequence",
                    Values.ppr(s.toString()) });
        }
        int len = seq.size();
        if (len == 0)
            return TupleValue.EmptyTuple;
        if (!(test instanceof OpLambdaValue) && !(test instanceof OpRcdValue))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "SelectSeq", "operator",
                    Values.ppr(test.toString()) });
        }
        ValueVec vals = new ValueVec();
        Applicable ftest = (Applicable) test;
        Value[] args = new Value[1];
        for (int i = 0; i < len; i++)
        {
            args[0] = seq.elems[i];
            Value val = ftest.apply(args, EvalControl.Clear);
            if (val instanceof IBoolValue)
            {
                if (((BoolValue) val).val)
                    vals.addElement(args[0]);
            } else
            {
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "SelectSeq",
                        "boolean-valued operator", Values.ppr(test.toString()) });
            }
        }
        Value[] elems = new Value[vals.size()];
        for (int i = 0; i < elems.length; i++)
        {
            elems[i] = vals.elementAt(i);
        }
        return new TupleValue(elems);
    }

    @Override
    public final int compareTo(Value s)
    {
        if ((s instanceof UserValue) && (((UserValue) s).userObj instanceof Sequences))
        {
            Sequences seq = (Sequences) ((UserValue) s).userObj;
            int cmp = this.size - seq.size;
            if (cmp == 0)
            {
                cmp = this.range.compareTo(seq.range);
            }
            return cmp;
        }
        if (s instanceof ModelValue)
        {
            return 1;
        }
        // SZ Jul 14, 2009:
        // replaced the message with a standard one, thrown by mismatch of compared elements
        throw new EvalException(EC.TLC_MODULE_COMPARE_VALUE, new String[] { Values.ppr(this.toString()),
                Values.ppr(s.toString()) });
    }

    @Override
    public final boolean member(Value s)
    {
        TupleValue seq = (TupleValue) s.toTuple();
        if (seq == null)
        {
            if (s instanceof ModelValue)
                return ((ModelValue) s).modelValueMember(this);
            throw new EvalException(EC.TLC_MODULE_CHECK_MEMBER_OF, new String[] { Values.ppr(s.toString()),
                    Values.ppr(this.toString()) });
        }
        int len = seq.size();
        if (len > this.size)
            return false;
        for (int i = 0; i < seq.elems.length; i++)
        {
            if (!this.range.member(seq.elems[i]))
                return false;
        }
        return true;
    }

    @Override
    public final boolean isFinite()
    {
        return this.size != Integer.MAX_VALUE;
    }

    @Override
    public final StringBuffer toString(StringBuffer sb, int offset, boolean swallow)
    {
        if (this.size == Integer.MAX_VALUE)
        {
            sb = sb.append("Seq(");
            sb = this.range.toString(sb, offset, swallow);
            sb = sb.append(")");
        } else
        {
            sb = sb.append("BSeq(");
            sb = this.range.toString(sb, offset, swallow);
            sb = sb.append(", ");
            sb = sb.append(this.size);
            sb = sb.append(")");
        }
        return sb;
    }

    public static Value Insert(Value s, Value v, Value test)
    {
        TupleValue seq = (TupleValue) s.toTuple();
        if (seq == null)
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "first", "Insert", "sequence",
                    Values.ppr(s.toString()) });
        }
        if (!(test instanceof Applicable))
        {
            throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "second", "SubSeq", "function",
                    Values.ppr(test.toString()) });
        }
        int len = seq.size();
        Applicable ftest = (Applicable) test;
        Value[] args = new Value[2];
        args[0] = v;
        Value[] values = new Value[len + 1];
        int idx = len;
        while (idx > 0)
        {
            args[1] = seq.elems[idx - 1];
            Value val = ftest.apply(args, EvalControl.Clear);
            if (!(val instanceof IBoolValue))
            {
                throw new EvalException(EC.TLC_MODULE_ARGUMENT_ERROR, new String[] { "third", "Insert",
                        "boolean-valued operator", Values.ppr(test.toString()) });
            }
            if (((BoolValue) val).val && v.compareTo(args[1]) < 0)
            {
                values[idx] = args[1];
                idx--;
            } else
            {
                values[idx] = v;
                break;
            }
        }
        if (idx == 0)
        {
            values[0] = v;
        } else
        {
            for (int i = idx - 1; i >= 0; i--)
            {
                values[i] = seq.elems[i];
            }
        }
        return new TupleValue(values);
    }

}
