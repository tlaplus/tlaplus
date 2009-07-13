// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at 10:07:06 PST by lamport
//      modified on Fri Aug 10 15:07:25 PDT 2001 by yuanyu

package tlc2.value;

import java.util.Arrays;

import tlc2.tool.EvalControl;
import tlc2.util.FP64;
import util.Assert;

public class FcnRcdValue extends Value implements Applicable {
  public Value[] domain;
  public IntervalValue intv;
  public Value[] values;
  private boolean isNorm;
  private int[] indexTbl;  // speed up function application

  /* Constructor */
  public FcnRcdValue(Value[] domain, Value[] values, boolean isNorm) {
    this.domain = domain;
    this.values = values;
    this.intv = null;
    this.isNorm = isNorm;
    this.indexTbl = null;
  }

  public FcnRcdValue(IntervalValue intv, Value[] values) {
    this.intv = intv;
    this.values = values;
    this.domain = null;
    this.isNorm = true;
    this.indexTbl = null;
  }

  private FcnRcdValue(FcnRcdValue fcn, Value[] values) {
    this.domain = fcn.domain;
    this.intv = fcn.intv;
    this.values = values;
    this.isNorm = fcn.isNorm;
    this.indexTbl = fcn.indexTbl;
  }

  public final byte getKind() { return FCNRCDVALUE; }

  /* We create an index only when the domain is not very small. */
  private final void createIndex() {
    if (this.domain != null && this.domain.length > 10) {
      int len = this.domain.length * 2 + 1;

      int[] tbl = new int[len];
      Arrays.fill(tbl, -1);

      synchronized(this) {
	for (int i = 0; i < this.domain.length; i++) {
	  int loc = (this.domain[i].hashCode() & 0x7FFFFFFF) % len;
	  while (tbl[loc] != -1) {
	    loc = (loc + 1) % len;
	  }
	  tbl[loc] = i;
	}
      }

      synchronized(this) { this.indexTbl = tbl; }
    }
  }

  private final int lookupIndex(Value arg) {
    int len = this.indexTbl.length;
    int loc = (arg.hashCode() & 0x7FFFFFFF) % len;
    while (true) {
      int idx = this.indexTbl[loc];
      if (idx == -1) {
	Assert.fail("Attempted to apply function:\n" + ppr(this.toString()) +
		    "\nto argument " + ppr(arg.toString()) +
		    ", which is not in the domain of the function.");
      }
      if (this.domain[idx].equals(arg)) {
	return idx;
      }
      loc = (loc + 1) % len;
    }
  }
  
  public final int compareTo(Object obj) {
    FcnRcdValue fcn = convert(obj);
    if (fcn == null) {
      if (obj instanceof ModelValue) return 1;
      Assert.fail("Attempted to compare the function " + ppr(this.toString()) +
		  " with the value:\n" + ppr(obj.toString()));
    }
    this.normalize();
    fcn.normalize();

    int result = this.values.length - fcn.values.length;
    if (result != 0) return result;

    if (this.intv != null) {
      if (fcn.intv != null) {
	result = this.intv.low - fcn.intv.low;
	if (result != 0) return result;
	for (int i = 0; i < this.values.length; i++) {
	  result = this.values[i].compareTo(fcn.values[i]);
	  if (result != 0) return result;
	}
      }
      else {
	for (int i = 0; i < fcn.domain.length; i++) {
	  Value dElem = fcn.domain[i];
	  if (!(dElem instanceof IntValue)) {
	    Assert.fail("Attempted to compare integer with non-integer:\n" +
			ppr(dElem.toString()) + ".");
	  }
	  result = this.intv.low + i - ((IntValue)dElem).val;
	  if (result != 0) return result;
	  result = this.values[i].compareTo(fcn.values[i]);
	  if (result != 0) return result;
	}
      }
    }
    else {
      if (fcn.intv != null) {
	for (int i = 0; i < this.domain.length; i++) {
	  Value dElem = this.domain[i];
	  if (!(dElem instanceof IntValue)) {
	    Assert.fail("Attempted to compare integer with non-integer\n" +
			ppr(dElem.toString()) + ".");
	  }
	  result = ((IntValue)dElem).val - (fcn.intv.low + i);
	  if (result != 0) return result;
	  result = this.values[i].compareTo(fcn.values[i]);
	  if (result != 0) return result;
	}
      }
      else {
	for (int i = 0; i < this.domain.length; i++) {
	  result = this.domain[i].compareTo(fcn.domain[i]);
	  if (result != 0) return result;
	  result = this.values[i].compareTo(fcn.values[i]);
	  if (result != 0) return result;
	}
      }
    }
    return 0;
  }

  public final boolean equals(Object obj) {
    FcnRcdValue fcn = convert(obj);
    if (fcn == null) {
      if (obj instanceof ModelValue) 
         return ((ModelValue) obj).modelValueEquals(this) ;
      Assert.fail("Attempted to check equality of the function " + ppr(this.toString()) +
		  " with the value:\n" + ppr(obj.toString()));
    }
    this.normalize();
    fcn.normalize();

    if (this.intv != null) {
      if (fcn.intv != null) {
	if (!this.intv.equals(fcn.intv)) return false;
	for (int i = 0; i < this.values.length; i++) {
	  if (!this.values[i].equals(fcn.values[i]))
	    return false;
	}
      }
      else {
	if (fcn.domain.length != this.intv.size()) return false;
	for (int i = 0; i < fcn.domain.length; i++) {
	  Value dElem = fcn.domain[i];
	  if (!(dElem instanceof IntValue)) {
	    Assert.fail("Attempted to compare an integer with non-integer:\n" +
			ppr(dElem.toString()) + ".");
	  }
	  if (((IntValue)dElem).val != (this.intv.low + i) ||
	      !this.values[i].equals(fcn.values[i])) {
	    return false;
	  }
	}
      }
    }
    else {
      if (this.values.length != fcn.values.length) return false;
      if (fcn.intv != null) {
	for (int i = 0; i < this.domain.length; i++) {
	  Value dElem = this.domain[i];
	  if (!(dElem instanceof IntValue)) {
	    Assert.fail("Attempted to compare an integer with non-integer:\n" +
			ppr(dElem.toString()) + ".");
	  }
	  if (((IntValue)dElem).val != (fcn.intv.low + i) ||
	      !this.values[i].equals(fcn.values[i])) {
	    return false;
	  }
	}
      }
      else {
	for (int i = 0; i < this.domain.length; i++) {
	  if (!this.domain[i].equals(fcn.domain[i]) ||
	      !this.values[i].equals(fcn.values[i])) {
	    return false;
	  }
	}
      }
    }
    return true;
  }

  public final boolean member(Value elem) {
    Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
		"\nis an element of the function " + ppr(this.toString()));
    return false;  // make compiler happy
  }

  public final boolean isFinite() { return true; }

  public final Value apply(Value arg, int control) {
    Value result = this.select(arg);
    if (result == null) {
      Assert.fail("Attempted to apply function:\n" + ppr(this.toString()) +
		  "\nto argument " + ppr(arg.toString()) + ", which is" +
		  " not in the domain of the function.");
    }
    return result;
  }

  /* This one does not seem to be needed anymore.  */
  public final Value apply(Value[] args, int control) {
    return this.apply(new TupleValue(args), EvalControl.Clear);
  }

  public final Value select(Value arg) {
    if (this.intv != null) {
      // domain is represented as an integer interval:
      if (!(arg instanceof IntValue)) {
	Assert.fail("Attempted to apply function with integer domain to" +
		    " the non-integer argument " + ppr(arg.toString()));
      }
      int idx = ((IntValue)arg).val;
      if ((idx >= this.intv.low) && (idx <= this.intv.high)) {
	return this.values[idx - this.intv.low];
      }
    }
    else {
      // domain is represented as an array of values:
      if (this.indexTbl != null) {
	return this.values[this.lookupIndex(arg)];
      }
      if (this.isNorm) this.createIndex();

      if (this.indexTbl != null) {
	return this.values[this.lookupIndex(arg)];
      }
      else {
	int len = this.domain.length;
	for (int i = 0; i < len; i++) {
	  if (this.domain[i].equals(arg)) {
	    return this.values[i];
	  }
	}
      }
    }
    return null;
  }

  public final boolean assign(Value[] args, Value val) {
    if (this.intv != null) {
      // domain is represented as an integer interval:
      if (args.length != 1) {
	Assert.fail("Wrong number of function arguments.");
      }
      if (args[0] instanceof IntValue) {
	int idx = ((IntValue)args[0]).val;
	if ((idx >= this.intv.low) && (idx <= this.intv.high)) {
	  int vIdx = idx - this.intv.low;
	  if (this.values[vIdx] == ValUndef ||
	      this.values[vIdx].equals(val)) {
	    this.values[vIdx] = val;
	    return true;
	  }
	  return false;
	}
      }
    }
    else {
      // domain is represented as an array of values:
      Value argv = new TupleValue(args);
      int len = this.domain.length;
      for (int i = 0; i < len; i++) {
	if (this.domain[i].equals(argv)) {
	  if (this.values[i] == ValUndef ||
	      this.values[i].equals(val)) {
	    this.values[i] = val;
	    return true;
	  }
	  return false;
	}
      }
    }
    Assert.fail("Function initialization out of domain.");
    return false;    // make compiler happy
  }
  
  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx >= ex.path.length) return ex.value;

    int flen = this.values.length;
    Value[] newValues = new Value[flen];
    for (int i = 0; i < flen; i++) {
      newValues[i] = this.values[i];
    }
    Value arg = ex.path[ex.idx];

    if (this.intv != null) {
      // domain is represented as an integer interval:
      if (arg instanceof IntValue) {
	int idx = ((IntValue)arg).val;
	if ((idx >= this.intv.low) && (idx <= this.intv.high)) {
	  int vidx = idx - this.intv.low;
	  ex.idx++;
	  newValues[idx] = this.values[vidx].takeExcept(ex);
	}
	return new FcnRcdValue(this.intv, newValues);
      }
    }
    else {
      // domain is represented as an array of values:
      for (int i = 0; i < flen; i++) {
	if (arg.equals(this.domain[i])) {
	  ex.idx++;
	  newValues[i] = newValues[i].takeExcept(ex);
	  Value[] newDomain = this.domain;
	  if (!this.isNorm) {
	    newDomain = new Value[flen];
	    for (int j = 0; j < flen; j++) {
	      newDomain[j] = this.domain[j];
	    }
	  }
	  return new FcnRcdValue(newDomain, newValues, this.isNorm);
	}
      }
    }
    return this;
  }

  public final Value takeExcept(ValueExcept[] exs) {
    Value res = this;
    for (int i = 0; i < exs.length; i++) {
      res = res.takeExcept(exs[i]);
    }
    return res;
  }

  public final Value getDomain() {
    if (this.intv != null) {
      return this.intv;
    }
    this.normalize();
    return new SetEnumValue(this.domain, true);
  }

  public final int size() {
    this.normalize();
    return this.values.length;
  }

  /*
   * This method converts a value to a function value. It returns
   * null if the conversion fails.
   */
  public static final FcnRcdValue convert(Object val) {
    switch (((Value)val).getKind()) {
    case FCNRCDVALUE:
      {
	return (FcnRcdValue)val;
      }
    case FCNLAMBDAVALUE:
      {
	return ((FcnLambdaValue)val).toFcnRcd();
      }
    case RECORDVALUE:
      {
	RecordValue rcd = (RecordValue)val;
	rcd.normalize();
	Value[] dom = new Value[rcd.names.length];
	for (int i = 0; i < rcd.names.length; i++) {
	  dom[i] = new StringValue(rcd.names[i]);
	}
	return new FcnRcdValue(dom, rcd.values, rcd.isNormalized());
      }
    case TUPLEVALUE:
      {
	Value[] elems = ((TupleValue)val).elems;
	IntervalValue intv = new IntervalValue(1, elems.length);
	return new FcnRcdValue(intv, elems);
      }
    default:
      // return null if not convertable
      return null;
    }
  }

  /* Return true iff this function is in normal form. */
  public final boolean isNormalized() { return this.isNorm; }
  
  /* This method normalizes (destructively) this function. */
  public final void normalize() {
    if (!this.isNorm) {
      // Assert.check(this.domain != null)
      int dlen = this.domain.length;
      for (int i = 1; i < dlen; i++) {
	int cmp = this.domain[0].compareTo(this.domain[i]);
	if (cmp == 0) {
	  Assert.fail("The value\n" + this.domain[i] +
		      "\noccurs multiple times in the function domain.");
	}
	else if (cmp > 0) {
	  Value tv = this.domain[0];
	  this.domain[0] = this.domain[i];
	  this.domain[i] = tv;
	  tv = this.values[0];
	  this.values[0] = this.values[i];
	  this.values[i] = tv;
	}
      }
      for (int i = 2; i < dlen; i++) {
	Value d = this.domain[i];
	Value v = this.values[i];
	int j = i;
	int cmp;
	while ((cmp = d.compareTo(this.domain[j-1])) < 0) {
	  this.domain[j] = this.domain[j-1];
	  this.values[j] = this.values[j-1];
	  j--;
	}
	if (cmp == 0) {
	  Assert.fail("The value\n" + this.domain[i] +
		      "\noccurs multiple times in the function domain.");
	}
	this.domain[j] = d;
	this.values[j] = v;
      }
      this.isNorm = true;
    }
  }

  public final boolean isDefined() {
    boolean defined = true;
    if (this.intv == null) {
      for (int i = 0; i < this.values.length; i++) {
	defined = defined && this.domain[i].isDefined();
      }
    }
    for (int i = 0; i < this.values.length; i++) {
      defined = defined && this.values[i].isDefined();
    }
    return defined;
  }

  public final Value deepCopy() {
    Value[] vals = new Value[this.values.length];
    for (int i = 0; i < vals.length; i++) {
      vals[i] = this.values[i].deepCopy();
    }
    return new FcnRcdValue(this, vals);
  }

  public final boolean assignable(Value val) {
    boolean canAssign = ((val instanceof FcnRcdValue) &&
			 this.values.length == ((FcnRcdValue)val).values.length);
    if (!canAssign) return false;
    FcnRcdValue fcn = (FcnRcdValue)val;
    for (int i = 0; i < this.values.length; i++) {
      canAssign = (canAssign &&
		   this.domain[i].equals(fcn.domain[i]) &&
		   this.values[i].assignable(fcn.values[i]));
    }
    return canAssign;
  }

  /* The fingerprint method.  */
  public final long fingerPrint(long fp) {
    this.normalize();
    int flen = this.values.length;
    fp = FP64.Extend(fp, FCNRCDVALUE);
    fp = FP64.Extend(fp, flen);
    if (this.intv == null) {
      for (int i = 0; i < flen; i++) {
	fp = this.domain[i].fingerPrint(fp);
	fp = this.values[i].fingerPrint(fp);
      }
    }
    else {
      for (int i = 0; i < flen; i++) {
	fp = FP64.Extend(fp, INTVALUE);
	fp = FP64.Extend(fp, i + this.intv.low);
	fp = this.values[i].fingerPrint(fp);
      }
    }
    return fp;
  }

  public final Value permute(MVPerm perm) {
    this.normalize();
    int flen = this.domain.length;
    Value[] vals = new Value[flen];

    boolean vchanged = false;
    for (int i = 0; i < flen; i++) {
      vals[i] = this.values[i].permute(perm);
      vchanged = vchanged || (vals[i] != this.values[i]);
    }

    if (this.intv == null) {
      Value[] dom = new Value[flen];
      boolean dchanged = false;
      for (int i = 0; i < flen; i++) {
	dom[i] = this.domain[i].permute(perm);
	dchanged = dchanged || (dom[i] != this.domain[i]);
      }

      if (dchanged) {
	return new FcnRcdValue(dom, vals, false);
      }
      else if (vchanged) {
	return new FcnRcdValue(this.domain, vals, true);
      }
    }
    else {
      if (vchanged) {
	return new FcnRcdValue(this.intv, vals);
      }
    }
    return this;
  }

  private static final boolean isName(String name) {
    int len = name.length();
    boolean hasLetter = false;

    for (int idx = 0; idx < len; idx++) {
      char ch = name.charAt(idx);
      if (ch == '_') continue;
      if (!Character.isLetterOrDigit(ch)) return false;
      hasLetter = hasLetter || Character.isLetter(ch);
    }

    return hasLetter && (len < 4 || (!name.startsWith("WF_") && !name.startsWith("SF_")));
  }

  private final boolean isRcd() {
    if (this.intv != null) return false;
    for (int i = 0; i < this.domain.length; i++) {
      Value dval = this.domain[i];
      boolean isName = ((dval instanceof StringValue) &&
			isName(((StringValue)dval).val.toString()));
      if (!isName) return false;
    }
    return true;
  }

  private final boolean isTuple() {
    if (this.intv != null) {
      return (this.intv.low == 1);
    }
    for (int i = 0; i < this.domain.length; i++) {
      if (!(this.domain[i] instanceof IntValue)) {
	return false;
      }
    }
    this.normalize();
    for (int i = 0; i < this.domain.length; i++) {
      if (((IntValue)this.domain[i]).val != (i+1)) {
	return false;
      }
    }
    return true;
  }
  
  /* The string representation of the value.  */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    int len = this.values.length;
    if (len == 0) {
      sb.append("<< >>");
    }
    else if (this.isRcd()) {
      sb.append("[");
      sb.append(((StringValue)this.domain[0]).val + " |-> ");
      sb = this.values[0].toString(sb, offset);

      for (int i = 1; i < len; i++) {
	sb.append(", ");
	sb.append(((StringValue)this.domain[i]).val + " |-> ");
	sb = this.values[i].toString(sb, offset);
      }
      sb.append("]");	
    }
    else if (this.isTuple()) {
      // It is actually a sequence:
      sb = sb.append("<<");
      sb = this.values[0].toString(sb, offset);

      for (int i = 1; i < len; i++) {
	sb.append(", ");
	sb = this.values[i].toString(sb, offset);
      }
      sb.append(">>");
    }
    else {
      sb = sb.append("(");
      sb = this.domain[0].toString(sb, offset);
      sb.append(" :> ");
      sb = this.values[0].toString(sb, offset);

      for (int i = 1; i < len; i++) {
	sb.append(" @@ ");
	sb = this.domain[i].toString(sb, offset);
	sb.append(" :> ");
	sb = this.values[i].toString(sb, offset);
      }
      sb.append(")");
    }
    return sb;
  }

}
