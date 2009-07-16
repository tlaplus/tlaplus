// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:35:58 PST by lamport
//      modified on Tue May 23 11:25:53 PDT 2000 by yuanyu

package tlc2.module;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.BoolValue;
import tlc2.value.Enumerable;
import tlc2.value.IntValue;
import tlc2.value.Value;
import tlc2.value.ValueConstants;

public class FiniteSets implements ValueConstants
{

    public static BoolValue IsFiniteSet(Value val)
    {
        return val.isFinite() ? ValTrue : ValFalse;
    }

    public static IntValue Cardinality(Value val)
    {
        if (val instanceof Enumerable)
        {
            return IntValue.gen(((Enumerable) val).size());
        }
        throw new EvalException(EC.TLC_MODULE_COMPUTING_CARDINALITY, Value.ppr(val.toString()));
    }

    // SZ 16.07.2009: commented the following code out, since it is not a part of FiniteSets
    /*
    public static Value setToList(Value set) {
      if (IsFiniteSet(set) == ValFalse) {
        throw new EvalException("setToList");
      }
      int size = Cardinality(set).val;
      Value[] elems = new Value[size];
      ValueEnumeration Enum = ((Enumerable)set).elements();
      Value val;
      int i = 0;
      while ((val = Enum.nextElement()) != null) {
        elems[i++] = val;
      }
      return new TupleValue(elems);
    }

    public static Value listToSet(Value list) {
      TupleValue tv = TupleValue.convert(list);
      if (tv == null) {
        throw new EvalException("listToSet");
      }
      Value[] elems = new Value[tv.size()];
      for (int i = 0; i < tv.size(); i++) {
        elems[i] = tv.elems[i];
      }
      return new SetEnumValue(elems, false);
    }
    
    public static Value appendSetToList(Value list, Value set) {
      TupleValue tv = TupleValue.convert(list);
      if (tv == null || IsFiniteSet(set) == ValFalse) {
        throw new EvalException("appendSetToList");
      }
      int lsz = tv.size();
      int ssz = Cardinality(set).val;
      Value[] elems = new Value[lsz+ssz];
      int i;
      for (i = 0; i < lsz; i++) {
        elems[i] = tv.elems[i];
      }
      ValueEnumeration Enum = ((Enumerable)set).elements();
      Value elem;
      while ((elem = Enum.nextElement()) != null) {
        elems[i++] = elem;
      }
      return new TupleValue(elems);
    }
    
    public static Value deleteSetFromList(Value set, Value list) {
      TupleValue tv = TupleValue.convert(list);
      if (tv == null) {
        throw new EvalException("deleteSetFromList");
      }
      ValueVec vals = new ValueVec();
      for (int i = 0; i < tv.size(); i++) {
        if (!set.member(tv.elems[i])) {
    vals.addElement(tv.elems[i]);
        }
      }
      Value[] elems = new Value[vals.size()];
      for (int i = 0; i < vals.size(); i++) {
        elems[i] = vals.elementAt(i);
      }
      return new TupleValue(elems);
    }
    
    public static Value keepSetFromList(Value set, Value list) {
      TupleValue tv = TupleValue.convert(list);
      if (tv == null) {
        throw new EvalException("keepSetFromList");
      }
      ValueVec vals = new ValueVec();
      for (int i = 0; i < tv.size(); i++) {
        if (set.member(tv.elems[i])) {
    vals.addElement(tv.elems[i]);
        }
      }
      Value[] elems = new Value[vals.size()];
      for (int i = 0; i < vals.size(); i++) {
        elems[i] = vals.elementAt(i);
      }
      return new TupleValue(elems);
    }
    */
}
