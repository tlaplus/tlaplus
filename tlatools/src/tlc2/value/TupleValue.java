// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:09 PST by lamport
//      modified on Fri Aug 10 15:10:22 PDT 2001 by yuanyu

package tlc2.value;

import tla2sany.semantic.SymbolNode;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.EvalControl;
import tlc2.util.Context;
import tlc2.util.FP64;
import util.Assert;

public class TupleValue extends Value implements Applicable {
  public Value[] elems;          // the elements of this tuple.

  /* Constructor */
  public TupleValue(Value[] elems) { this.elems = elems; }

  public TupleValue(Value v) {
    this.elems = new Value[1];
    this.elems[0] = v;
  }
  
  public TupleValue(Value v1, Value v2) {
    this.elems = new Value[2];
    this.elems[0] = v1;
    this.elems[1] = v2;
  }
  
  public final byte getKind() { return TUPLEVALUE; }

  public final int compareTo(Object obj) {
    TupleValue tv = convert(obj);
    if (tv == null) {
      // Well, we have to convert this to function and compare.
      return FcnRcdValue.convert(this).compareTo(obj);
    }
    int len = this.elems.length;
    int cmp = len - tv.elems.length;
    if (cmp == 0) {
      for (int i = 0; i < len; i++) {
	cmp = this.elems[i].compareTo(tv.elems[i]);
	if (cmp != 0) break;
      }
    }
    return cmp;
  }

  public final boolean equals(Object obj) {
    TupleValue tv = convert(obj);
    if (tv == null) {
      // Well, we have to convert this to function and compare.
      return FcnRcdValue.convert(this).equals(obj);
    }
    int len = this.elems.length;
    if (len != tv.elems.length)
      return false;
    for (int i = 0; i < len; i++) {
      if (!this.elems[i].equals(tv.elems[i]))
	return false;
    }
    return true;
  }

  public final boolean member(Value elem) {
    Assert.fail("Attempted to check set membership in a tuple value.");
    return false;   // make compiler happy
  }

  public final boolean isFinite() { return true; }
  
  public final Value apply(Value arg, int control) {
    if (!(arg instanceof IntValue)) {
      Assert.fail("Attempted to apply tuple to a non-integer argument.");
    }
    int idx = ((IntValue)arg).val;
    if (idx <= 0 || idx > this.elems.length) {
      Assert.fail("Attempted to apply tuple\n" + ppr(this.toString()) +
		  "\nto integer " + idx + " which is out of domain.");
    }
    return this.elems[idx-1];
  }

  public final Value apply(Value[] args, int control) {
    if (args.length != 1) {
      Assert.fail("Attetmpted to apply tuple with wrong number of arguments.");
    }
    return this.apply(args[0], EvalControl.Clear);
  }
  
  public final Value select(Value arg) {
    if (!(arg instanceof IntValue)) {
      Assert.fail("Attempted to apply tuple to a non-integer argument " +
		  ppr(arg.toString()) + ".");		  
    }
    int idx = ((IntValue)arg).val;
    if (idx > 0 && idx <= this.elems.length) {
      return this.elems[idx-1];
    }
    return null;
  }

  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx < ex.path.length) {
      int tlen = this.elems.length;
      Value[] newElems = new Value[tlen];
      Value arcVal = ex.path[ex.idx];
      if (arcVal instanceof IntValue) {
	int idx = ((IntValue)arcVal).val - 1;
	if (0 <= idx && idx < tlen) {
	  for (int i = 0; i < tlen; i++) {
	    newElems[i] = this.elems[i];
	  }
	  ex.idx++;
	  newElems[idx] = this.elems[idx].takeExcept(ex);
	}
	return new TupleValue(newElems);
      }
      MP.printWarning(EC.TLC_WRONG_TUPLE_FIELD_NAME, new String[]{ppr(arcVal.toString())});
    }
    return ex.value;
  }

  public final Value takeExcept(ValueExcept[] exs) {
    Value val = this;
    for (int i = 0; i < exs.length; i++) {
      val = val.takeExcept(exs[i]);
    }
    return val;
  }

  public final Value getDomain() {
    return new IntervalValue(1, this.size());
  }
  
  public final int size() { return this.elems.length; }

  /*
   * This method converts a value to a tuple value. It returns
   * null if the conversion fails.
   */
  public static TupleValue convert(Object val) {
    if (val instanceof TupleValue) {
      return (TupleValue)val;
    }
    else if (val instanceof FcnRcdValue) {
      FcnRcdValue fcn = (FcnRcdValue)val;
      if (fcn.intv != null) {
	if (fcn.intv.low != 1) return null;
	return new TupleValue(fcn.values);
      }
      int len = fcn.values.length;
      Value[] elems = new Value[len];
      for (int i = 0; i < len; i++) {
	if (!(fcn.domain[i] instanceof IntValue)) return null;
	int idx = ((IntValue)fcn.domain[i]).val;
	if (0 < idx && idx <= len) {
	  if (elems[idx-1] != null) return null;
	  elems[idx-1] = fcn.values[i];
	}
	else {
	  return null;
	}
      }
      return new TupleValue(elems);
    }
    else if (val instanceof FcnLambdaValue) {
      FcnLambdaValue fcn = (FcnLambdaValue)val;
      if (fcn.params.length() != 1) return null;
      Value dom = fcn.params.domains[0];
      SymbolNode var = fcn.params.formals[0][0];
      if (dom instanceof IntervalValue) {
	IntervalValue intv = (IntervalValue)dom;
	if (intv.low != 1) return null;
	Value[] elems = new Value[intv.high];
	for (int i = 1; i <= intv.high; i++) {
	  Context c1 = fcn.con.cons(var, IntValue.gen(i));
	  elems[i-1] = fcn.tool.eval(fcn.body, c1, fcn.state, fcn.pstate, fcn.control);
	}
	return new TupleValue(elems);
      }
      else {
	SetEnumValue eSet = SetEnumValue.convert(dom);
	if (eSet == null)
	  Assert.fail("To convert a function of form [x \\in S |-> f(x)] " +
		      "to a tuple, the set S must be enumerable.");
	eSet.normalize();
	int len = eSet.size();
	Value[] elems = new Value[len];
	for (int i = 0; i < len; i++) {
	  Value argVal = eSet.elems.elementAt(i);
	  if (!(argVal instanceof IntValue)) return null;
	  if (((IntValue)argVal).val != i + 1) return null;
	  Context c1 = fcn.con.cons(var, argVal);
	  elems[i] = fcn.tool.eval(fcn.body, c1, fcn.state, fcn.pstate, fcn.control);
	}
	return new TupleValue(elems);	
      }
    }
    else if ((val instanceof RecordValue) &&
	     ((RecordValue)val).size() == 0) {
      return EmptyTuple;
    }
    return null;
  }

  /* The normalization of the value. */
  public final boolean isNormalized() { return true; }
  
  public final void normalize() { /*nop*/ }

  public final boolean isDefined() {
    boolean defined = true;
    for (int i = 0; i < this.elems.length; i++) {
      defined = defined && this.elems[i].isDefined();
    }
    return defined;
  }

  public final Value deepCopy() {
    Value[] vals = new Value[this.elems.length];
    for (int i = 0; i < this.elems.length; i++) {
      vals[i] = this.elems[i].deepCopy();
    }
    return new TupleValue(vals);
  }

  public final boolean assignable(Value val) {
    boolean canAssign = ((val instanceof TupleValue) &&
			 (this.elems.length == ((TupleValue)val).elems.length));
    if (!canAssign) return false;
    for (int i = 0; i < this.elems.length; i++) {
      canAssign = canAssign && this.elems[i].assignable(((TupleValue)val).elems[i]);
    }
    return canAssign;
  }
  
  /* The fingerprint method: tuples are functions. */
  public final long fingerPrint(long fp) {
    int len = this.elems.length;
    fp = FP64.Extend(fp, FCNRCDVALUE);
    fp = FP64.Extend(fp, len);
    for (int i = 0; i < len; i++) {
      fp = FP64.Extend(fp, INTVALUE);
      fp = FP64.Extend(fp, i+1);
      fp = this.elems[i].fingerPrint(fp);
    }
    return fp;
  }

  public final Value permute(MVPerm perm) {
    Value[] vals = new Value[this.elems.length];
    boolean changed = false;
    for (int i = 0; i < vals.length; i++) {
      vals[i] = this.elems[i].permute(perm);
      changed = changed || (vals[i] != this.elems[i]);
    }
    if (changed) {
      return new TupleValue(vals);
    }
    return this;
  }

  /* The string representation of this value. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    sb.append("<<");
    int len = this.elems.length;
    if (len > 0) {
      sb = this.elems[0].toString(sb, offset);
    }
    for (int i = 1; i < len; i++) {
      sb = sb.append(", ");
      sb = this.elems[i].toString(sb, offset);
    }
    sb.append(">>");
    return sb;
  }

}
