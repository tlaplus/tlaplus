// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:19:45 PST by lamport
//      modified on Tue Aug  7 10:46:55 PDT 2001 by yuanyu

package tlc2.module;

import tlc2.TLCGlobals;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.TLARegistry;
import tlc2.tool.Worker;
import tlc2.util.RandomGenerator;
import tlc2.value.Applicable;
import tlc2.value.BoolValue;
import tlc2.value.FcnRcdValue;
import tlc2.value.IntValue;
import tlc2.value.IntervalValue;
import tlc2.value.RecordValue;
import tlc2.value.SetEnumValue;
import tlc2.value.SetOfFcnsValue;
import tlc2.value.SetOfRcdsValue;
import tlc2.value.SetOfTuplesValue;
import tlc2.value.StringValue;
import tlc2.value.TupleValue;
import tlc2.value.Value;
import tlc2.value.ValueConstants;
import tlc2.value.ValueVec;
import util.Assert;
import util.ToolIO;

public class TLC implements ValueConstants {

  private static RandomGenerator rng;
  
  static {
    Assert.check(TLARegistry.put("MakeFcn", ":>") == null);
    Assert.check(TLARegistry.put("CombineFcn", "@@") == null);
    rng = new RandomGenerator();
  }

  /**
   * Prints to standard error the string (v1 + "  " + v2), and
   * returns the value v2.
   */
  public static Value Print(Value v1, Value v2) {
      ToolIO.err.println(Value.ppr(v1.toString()) + "  " + Value.ppr(v2.toString()));
      return v2;
  }

  /**
   * Prints to standard error the string v1. Always returns TRUE.
   */
  public static Value PrintT(Value v1) {
      ToolIO.err.println(Value.ppr(v1.toString()));
      return ValTrue;
  }

  /* Returns the string value of the string representation of v. */
  public static Value ToString(Value v) {
    return new StringValue(v.toString());
  }
  
  /**
   * Returns true if the value of v1 is true. Otherwise, throws
   * an exception with v2 as the error message.
   */
  public static Value Assert(Value v1, Value v2) {
    if ((v1 instanceof BoolValue) && ((BoolValue)v1).val) {
      return v1;
    }
    String msg = "The first argument of Assert evaluated to FALSE; the" +
      " second argument was:\n" + Value.ppr(v2.toString());
    throw new EvalException(EvalException.ASSERT, msg);
  }

  /**
   * The current wall clock time.  Note that it is not declared as final.
   * So, TLC will not treat it as a constant.
   */
  public static Value JavaTime() {
    int t = (int)System.currentTimeMillis();
    return IntValue.gen(t & 0x7FFFFFFF);
  }

  public static Value TLCGet(Value vidx) {
    if (vidx instanceof IntValue) {
      int idx = ((IntValue)vidx).val;
      if (idx >= 0) {
	Thread th = Thread.currentThread();
	Value res = null;
	if (th instanceof Worker) {
	  res = ((Worker)th).getLocalValue(idx);	  
	}
	else {
	  res = tlc2.TLCGlobals.mainChecker.getValue(0, idx);
	}
	if (res == null) {
	  String msg = "TLCGet(" + idx + ") was undefined.";
	  throw new EvalException(EvalException.ASSERT, msg);
	}
	return res;
      }
    }
    String msg = "The argument of TLCGet should be a nonnegative integer," +
      " but instead it is:\n" + Value.ppr(vidx.toString());
    throw new EvalException(EvalException.ASSERT, msg);
  }
  
  public static Value TLCSet(Value vidx, Value val) {
    if (vidx instanceof IntValue) {
      int idx = ((IntValue)vidx).val;
      if (idx >= 0) {
	Thread th = Thread.currentThread();
	if (th instanceof Worker) {
	  ((Worker)th).setLocalValue(idx, val);
	}
	else {
	  TLCGlobals.mainChecker.setAllValues(idx, val);
	}
	return ValTrue;
      }
    }
    String msg = "The first argument of TLCSet should be a nonnegative integer," +
      " but instead it is:\n" + Value.ppr(vidx.toString());
    throw new EvalException(EvalException.ASSERT, msg);
  }
  
  public static Value MakeFcn(Value d, Value e) {
    Value[] dom = new Value[1];
    Value[] vals = new Value[1];
    dom[0] = d;
    vals[0] = e;
    return new FcnRcdValue(dom, vals, true);
  }

  public static Value CombineFcn(Value f1, Value f2) {
    FcnRcdValue fcn1 = FcnRcdValue.convert(f1);
    FcnRcdValue fcn2 = FcnRcdValue.convert(f2);
    if (fcn1 == null) {
      String msg = "The first argument of @@ should be a " +
	"function; but instead it is:\n" + Value.ppr(f1.toString());
      throw new EvalException(msg);
    }
    if (fcn2 == null) {
      String msg = "The second argument of @@ should be a " +
	"function; but instead it is:\n" + Value.ppr(f1.toString());
      throw new EvalException(msg);
    }
    ValueVec dom = new ValueVec();
    ValueVec vals = new ValueVec();
    Value[] vals1 = fcn1.values;
    Value[] vals2 = fcn2.values;

    Value[] dom1 = fcn1.domain;
    if (dom1 == null) {
      IntervalValue intv1 = fcn1.intv;
      for (int i = intv1.low; i <= intv1.high; i++) {
	dom.addElement(IntValue.gen(i));
	vals.addElement(vals1[i]);
      }
    }
    else {
      for (int i = 0; i < dom1.length; i++) {
	dom.addElement(dom1[i]);
	vals.addElement(vals1[i]);
      }
    }

    int len1 = dom.size();
    Value[] dom2 = fcn2.domain;
    if (dom2 == null) {
      IntervalValue intv2 = fcn2.intv;
      for (int i = intv2.low; i <= intv2.high; i++) {
	Value val = IntValue.gen(i);
	boolean found = false;
	for (int j = 0; j < len1; j++) {
	  if (val.equals(dom.elementAt(j))) {
	    found = true; break;
	  }
	}
	if (!found) {
	  dom.addElement(val);
	  vals.addElement(vals2[i]);
	}
      }
    }
    else {
      for (int i = 0; i < dom2.length; i++) {
	Value val = dom2[i];
	boolean found = false;
	for (int j = 0; j < len1; j++) {
	  if (val.equals(dom.elementAt(j))) {
	    found = true; break;
	  }
	}
	if (!found) {
	  dom.addElement(val);
	  vals.addElement(vals2[i]);
	}
      }
    }

    Value[] domain = new Value[dom.size()];
    Value[] values = new Value[dom.size()];
    for (int i = 0; i < domain.length; i++) {
      domain[i] = dom.elementAt(i);
      values[i] = vals.elementAt(i);
    }
    return new FcnRcdValue(domain, values, false);
  }

  public static Value SortSeq(Value s, Value cmp) {
    TupleValue seq = TupleValue.convert(s);
    if (seq == null) {
      String msg = "The first argument of SortSeq should be a " +
	"natural number; but instead it is:\n" + Value.ppr(s.toString());
      throw new EvalException(msg);
    }
    if (!(cmp instanceof Applicable)) {
      String msg = "The second argument of SortSeq must be a " +
	"function, but instead it is\n" + Value.ppr(cmp.toString());
      throw new EvalException(msg);
    }
    Applicable fcmp = (Applicable)cmp;
    Value[] elems = seq.elems;
    int len = elems.length;
    if (len == 0) return seq;
    Value[] args = new Value[2];
    Value[] newElems = new Value[len];
    newElems[0] = elems[0];
    for (int i = 1; i < len; i++) {
      int j = i;
      args[0] = elems[i];
      args[1] = newElems[j-1];
      while (compare(fcmp, args)) {
	newElems[j] = newElems[j-1];
	j--;
	if (j == 0) break;
	args[1] = newElems[j-1];
      }
      newElems[j] = args[0];
    }
    return new TupleValue(newElems);
  }

  private static boolean compare(Applicable fcmp, Value[] args) {
    Value res = fcmp.apply(args, EvalControl.Clear);
    if (res instanceof BoolValue) {
      return ((BoolValue)res).val;
    }
    String msg = "The second argument of SortSeq must be a " +
      "boolean function; but it returns:\n" + Value.ppr(res.toString());
    throw new EvalException(msg);
  }

  public static Value Permutations(Value s) {
    SetEnumValue s1 = SetEnumValue.convert(s);
    if (s1 == null) {
      String msg = "Applying Permutations to the following value,\n" +
	"which is not a finite set:\n" + Value.ppr(s.toString());
      throw new EvalException(msg);
    }
    s1.normalize();
    ValueVec elems = s1.elems;
    int len = elems.size();
    if (len == 0) {
      Value[] elems1 = {EmptyFcn};
      return new SetEnumValue(elems1, true);
    }

    Value[] domain = new Value[len];
    for (int i = 0; i < len; i++) {
      domain[i] = elems.elementAt(i);
    }
    int[] idxArray = new int[len];
    boolean[] inUse = new boolean[len];
    for (int i = 0; i < len; i++) {
      idxArray[i] = i;
      inUse[i] = true;
    }
    
    ValueVec fcns = new ValueVec();
  _done:
    while (true) {
      Value[] vals = new Value[len];
      for (int i = 0; i < len; i++) {
	vals[i] = domain[idxArray[i]];
      }
      fcns.addElement(new FcnRcdValue(domain, vals, true));
      int i;
      for (i = len-1; i >= 0; i--) {
	boolean found = false;
	for (int j = idxArray[i]+1; j < len; j++) {
	  if (!inUse[j]) {
	    inUse[j] = true;
	    inUse[idxArray[i]] = false;
	    idxArray[i] = j;
	    found = true;
	    break;
	  }
	}
	if (found) break;
	if (i == 0) break _done;
	inUse[idxArray[i]] = false;	  
      }
      for (int j = i+1; j < len; j++) {
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

  public static Value RandomElement(Value val) {
    switch (val.getKind()) {
    case SETOFFCNSVALUE:
      {
	SetOfFcnsValue sfv = (SetOfFcnsValue)val;
	sfv.normalize();
	SetEnumValue domSet = SetEnumValue.convert(sfv.domain);
	if (domSet == null) {
	   String msg = "Applying RandomElement to the following value,\n" +
	     "which is not a finite set:\n" + Value.ppr(val.toString());
	   throw new EvalException(msg);
	}
	domSet.normalize();
	ValueVec elems = domSet.elems;	
	Value[] dom = new Value[elems.size()];
	Value[] vals = new Value[elems.size()];
	for (int i = 0; i < dom.length; i++) {
	  dom[i] = elems.elementAt(i);
	  vals[i] = RandomElement(sfv.range);
	}
	return new FcnRcdValue(dom, vals, true);
      }
    case SETOFRCDSVALUE:
      {
	SetOfRcdsValue srv = (SetOfRcdsValue)val;
	srv.normalize();
	Value[] vals = new Value[srv.names.length];
	for (int i = 0; i < vals.length; i++) {
	  vals[i] = RandomElement(srv.values[i]);
	}
	return new RecordValue(srv.names, vals, true);
      }
    case SETOFTUPLESVALUE:
      {
	SetOfTuplesValue stv = (SetOfTuplesValue)val;
	stv.normalize();
	Value[] vals = new Value[stv.sets.length];
	for (int i = 0; i < vals.length; i++) {
	  vals[i] = RandomElement(stv.sets[i]);
	}
	return new TupleValue(vals);
      }
    default:
      {
	SetEnumValue enumVal = SetEnumValue.convert(val);
	if (enumVal == null) {
	  String msg = "Applying RandomElement to the following value,\n" +
	    "which is not a finite set:\n" + Value.ppr(val.toString());
	  throw new EvalException(msg);
	}
	int sz = enumVal.size();
	int index = (int)Math.floor(rng.nextDouble() * sz);
	return enumVal.elems.elementAt(index);
      }
    }
  }

  public static Value Any() { return AnySet.ANY(); }
  
  /**
  public static Value FApply(Value f, Value op, Value base) {
    FcnRcdValue fcn = FcnRcdValue.convert(f);
    if (fcn == null) {
      String msg = "The first argument of FApply must be a " +
	"function with finite domain, but instead it is\n" +
	Value.ppr(f.toString());
      throw new EvalException(msg);
    }
    if (!(op instanceof Applicable)) {
      String msg = "The second argument of FApply must be a " +
	"function, but instead it is\n" + Value.ppr(op.toString());
      throw new EvalException(msg);
    }
    Value[] args = new Value[2];
    Applicable op1 = (Applicable)op;
    args[0] = base;
    for (int i = 0; i < fcn.values.length; i++) {
      args[1] = fcn.values[i];
      args[0] = op1.apply(args, false);
    }
    return args[0];
  }
  
  public static Value FSum(Value f) {
    FcnRcdValue fcn = FcnRcdValue.convert(f);
    if (fcn == null) {
      String msg = "The argument of FSum should be a function; " +
	"but instead it is:\n" + Value.ppr(f.toString());
      throw new EvalException(msg);
    }
    Value[] vals = fcn.values;
    int sum = 0;
    for (int i = 0; i < vals.length; i++) {
      if (!(vals[i] instanceof IntValue)) {
	String msg = "The argument of FSum should be a function " +
	  "with integer range; but instead it is:\n" + Value.ppr(f.toString());
	throw new EvalException(msg);
      }
      sum += ((IntValue)vals[i]).val;
    }
    return IntValue.gen(sum);
  }
  **/
}
