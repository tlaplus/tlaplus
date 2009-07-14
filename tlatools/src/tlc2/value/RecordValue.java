// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at 10:15:47 PST by lamport
//      modified on Fri Aug 10 15:09:07 PDT 2001 by yuanyu

package tlc2.value;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.util.FP64;
import util.Assert;
import util.UniqueString;

public class RecordValue extends Value implements Applicable {
  public UniqueString[] names;   // the field names
  public Value[] values;         // the field values
  private boolean isNorm;
  
  /* Constructor */
  public RecordValue(UniqueString[] names, Value[] values, boolean isNorm) {
    this.names = names;
    this.values = values;
    this.isNorm = isNorm;
  }

  public final byte getKind() { return RECORDVALUE; }

  public final int compareTo(Object obj) {
    RecordValue rcd = convert(obj);
    if (rcd == null) {
      if (obj instanceof ModelValue) return 1;
      Assert.fail("Attempted to compare record:\n" + ppr(this.toString()) +
		  "\nwith non-record\n" + ppr(obj.toString()));
    }
    this.normalize();
    rcd.normalize();
    int len = this.names.length;
    int cmp = len - rcd.names.length;
    if (cmp == 0) {
      for (int i = 0; i < len; i++) {
	cmp = this.names[i].compareTo(rcd.names[i]);
	if (cmp != 0) break;
	cmp = this.values[i].compareTo(rcd.values[i]);
	if (cmp != 0) break;
      }
    }
    return cmp;
  }

  public final boolean equals(Object obj) {
    RecordValue rcd = convert(obj);
    if (rcd == null) {
      if (obj instanceof ModelValue) 
         return ((ModelValue) obj).modelValueEquals(this) ;
      Assert.fail("Attempted to check equality of record:\n" + ppr(this.toString()) +
		  "\nwith non-record\n" + ppr(obj.toString()));
    }
    this.normalize();
    rcd.normalize();
    int len = this.names.length;
    if (len != rcd.names.length) return false;
    for (int i = 0; i < len; i++) {
      if ((!(this.names[i].equals(rcd.names[i]))) ||
	  (!(this.values[i].equals(rcd.values[i]))))
	return false;
    }
    return true;
  }

  public final boolean member(Value elem) {
    Assert.fail("Attempted to check if element:\n" + ppr(elem.toString()) +
                "\nis in the record:\n" + ppr(this.toString()));
    return false;    // make compiler happy
  }

  public final boolean isFinite() { return true; }
  
  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx < ex.path.length) {
      int rlen = this.names.length;
      Value[] newValues = new Value[rlen];
      Value arcVal = ex.path[ex.idx];
      if (arcVal instanceof StringValue) {
	UniqueString arc = ((StringValue)arcVal).val;
	for (int i = 0; i < rlen; i++) {
	  if (this.names[i].equals(arc)) {
	    ex.idx++;
	    newValues[i] = this.values[i].takeExcept(ex);
	  }
	  else {
	    newValues[i] = this.values[i];
	  }
	}
	UniqueString[] newNames = this.names;
	if (!this.isNorm) {
	  newNames = new UniqueString[rlen];
	  for (int i = 0; i < rlen; i++) {
	    newNames[i] = this.names[i];
	  }
	}
	return new RecordValue(newNames, newValues, this.isNorm);
      }
      else {
          MP.printWarning(EC.TLC_WRONG_RECORD_FIELD_NAME, new String[]{ppr(arcVal.toString())});
      }
    }
    return ex.value;
  }

  public final Value takeExcept(ValueExcept[] exs) {
    Value res = this;
    for (int i = 0; i < exs.length; i++) {
      res = res.takeExcept(exs[i]);
    }
    return res;
  }

  /*
   * This method converts a value to a function value. It returns
   * null if the conversion fails.
   */
  public static final RecordValue convert(Object val) {
    if (val instanceof RecordValue) {
      return (RecordValue)val;
    }
    else if (val instanceof FcnRcdValue ||
	     val instanceof FcnLambdaValue) {
      FcnRcdValue fcn = FcnRcdValue.convert(val);
      if (fcn == null || fcn.domain == null) return null;
      fcn.normalize();
      UniqueString[] vars = new UniqueString[fcn.domain.length];
      for (int i = 0; i < fcn.domain.length; i++) {
	if (!(fcn.domain[i] instanceof StringValue)) {
	  return null;
	}
	vars[i] = ((StringValue)fcn.domain[i]).getVal();
      }
      return new RecordValue(vars, fcn.values, fcn.isNormalized());
    }
    else if ((val instanceof TupleValue) &&
	     ((TupleValue)val).size() == 0) {
      return EmptyRcd;
    }
    // return null if not convertable
    return null;
  }
  
  public final int size() { return this.names.length; }

  public final Value apply(Value arg, int control) {
    if (!(arg instanceof StringValue)) {
      Assert.fail("Attempted to apply record to a non-string value " +
		  ppr(arg.toString()) + ".");
    }
    UniqueString name = ((StringValue)arg).getVal();    
    int rlen = this.names.length;
    for (int i = 0; i < rlen; i++) {
      if (name.equals(this.names[i])) {
	return this.values[i];
      }
    }
    Assert.fail("Attempted to apply the record\n" + ppr(this.toString()) +
		"\nto nonexistent record field " + name + ".");
    return null;    // make compiler happy
  }

  public final Value apply(Value[] args, int control) {
    if (args.length != 1) {
      Assert.fail("Attempted to apply record to more than one arguments.");
    }
    return this.apply(args[0], control);
  }

  /* This method returns the named component of the record. */
  public final Value select(Value arg) {
    if (!(arg instanceof StringValue)) {
      Assert.fail("Attempted to apply record to a non-string argument " +
		  ppr(arg.toString()) + ".");
    }
    UniqueString name = ((StringValue)arg).getVal();    
    int rlen = this.names.length;
    for (int i = 0; i < rlen; i++) {
      if (name.equals(this.names[i])) {
	return this.values[i];
      }
    }
    return null;
  }

  public final Value getDomain() {
    Value[] dElems = new Value[this.names.length];
    for (int i = 0; i < this.names.length; i++) {
      dElems[i] = new StringValue(this.names[i]);
    }
    return new SetEnumValue(dElems, this.isNormalized());
  }

  public final boolean assign(UniqueString name, Value val) {
    for (int i = 0; i < this.names.length; i++) {
      if (name.equals(this.names[i])) {
	if (this.values[i] == ValUndef ||
	    this.values[i].equals(val)) {
	  this.values[i] = val;
	  return true;
	}
	return false;
      }
    }
    Assert.fail("Attempted to assign to nonexistent record field " + name + ".");
    return false;    // make compiler happy
  }

  public final boolean isNormalized() { return this.isNorm; }
  
  public final void normalize() {
    if (!this.isNorm) {
      int len = this.names.length;
      for (int i = 1; i < len; i++) {
	int cmp = this.names[0].compareTo(this.names[i]);
	if (cmp == 0) {
	  Assert.fail("Field name " + this.names[i] + " occurs multiple times in record.");
	}
	else if (cmp > 0) {
	  UniqueString ts = this.names[0];
	  this.names[0] = this.names[i];
	  this.names[i] = ts;
	  Value tv = this.values[0];
	  this.values[0] = this.values[i];
	  this.values[i] = tv;
	}
      }
      for (int i = 2; i < len; i++) {
	int j = i;
	UniqueString st = this.names[i];
	Value val = this.values[i];
	int cmp;
	while ((cmp = st.compareTo(this.names[j-1])) < 0) {
	  this.names[j] = this.names[j-1];
	  this.values[j] = this.values[j-1];
	  j--;
	}
	if (cmp == 0) {
	  Assert.fail("Field name " + this.names[i] + " occurs multiple times in record.");
	}
	this.names[j] = st;
	this.values[j] = val;
      }
      this.isNorm = true;
    }
  }

  public final boolean isDefined() {
    boolean defined = true;
    for (int i = 0; i < this.values.length; i++) {
      defined = defined && this.values[i].isDefined();
    }
    return defined;
  }

  public final Value deepCopy() {
    Value[] vals = new Value[this.values.length];
    for (int i = 0; i < this.values.length; i++) {
      vals[i] = this.values[i].deepCopy();
    }
    return new RecordValue(this.names, vals, this.isNorm);
  }

  public final boolean assignable(Value val) {
    boolean canAssign = ((val instanceof RecordValue) &&
			 this.names.length == ((RecordValue)val).names.length);
    if (!canAssign) return false;
    for (int i = 0; i < this.values.length; i++) {
      canAssign = (canAssign &&
		   this.names[i].equals(((RecordValue)val).names[i]) &&
		   this.values[i].assignable(((RecordValue)val).values[i]));
    }
    return canAssign;
  }
  
  /* The fingerprint methods.  */
  public final long fingerPrint(long fp) {
    this.normalize();
    int rlen = this.names.length;
    fp = FP64.Extend(fp, FCNRCDVALUE);
    fp = FP64.Extend(fp, rlen);
    for (int i = 0; i < rlen; i++) {
      String str = this.names[i].toString();
      fp = FP64.Extend(fp, STRINGVALUE);
      fp = FP64.Extend(fp, str.length());
      fp = FP64.Extend(fp, str);
      fp = this.values[i].fingerPrint(fp);
    }
    return fp;
  }

  public final Value permute(MVPerm perm) {
    this.normalize();
    int rlen = this.names.length;
    Value[] vals = new Value[rlen];
    boolean changed = false;
    for (int i = 0; i < rlen; i++) {
      vals[i] = this.values[i].permute(perm);
      changed = changed || (vals[i] != this.values[i]);
    }
    if (changed) {
      return new RecordValue(this.names, vals, true);
    }
    return this;
  }

  /* The string representation */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    int len = this.names.length;

    sb.append("[");
    if (len > 0) {
      sb.append(this.names[0] + " |-> ");
      sb = this.values[0].toString(sb, offset);
    }
    for (int i = 1; i < len; i++) {
      sb.append(", ");
      sb.append(this.names[i] + " |-> ");
      sb = this.values[i].toString(sb, offset);
    }
    return sb.append("]");
  }

}
