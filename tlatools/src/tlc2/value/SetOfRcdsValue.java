// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at 10:18:01 PST by lamport
//      modified on Fri Aug 10 15:09:53 PDT 2001 by yuanyu

package tlc2.value;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import util.Assert;
import util.UniqueString;

public class SetOfRcdsValue extends Value implements Enumerable {
  public UniqueString[] names;      // The names of the fields.
  public Value[] values;            // The values of the fields.
  protected SetEnumValue rcdSet;
  
  /* Constructor */
  public SetOfRcdsValue(UniqueString[] names, Value[] values, boolean isNorm) {
    this.names = names;
    this.values = values;
    this.rcdSet = null;
    if (!isNorm) {
      this.sortByNames();
    }
  }

  public final byte getKind() { return SETOFRCDSVALUE; }

  public final int compareTo(Object obj) {
    this.convertAndCache();
    return this.rcdSet.compareTo(obj);    
  }
  
  public final boolean equals(Object obj) {
    if (obj instanceof SetOfRcdsValue) {
      SetOfRcdsValue rcds = (SetOfRcdsValue)obj;
      if (this.names.length != rcds.names.length) {
	return false;
      }
      for (int i = 0; i < this.names.length; i++) {
	if (!this.names[i].equals(rcds.names[i]) ||
	    !this.values[i].equals(rcds.values[i])) {
	  return false;
	}
      }
      return true;
    }
    this.convertAndCache();
    return this.rcdSet.equals(obj);
  }

  public final boolean member(Value elem) {
    RecordValue rcd = RecordValue.convert(elem);
    if (rcd == null) {
      if (elem instanceof ModelValue)   
         return ((ModelValue) elem).modelValueMember(this) ;
      Assert.fail("Attempted to check if non-record\n" + elem + "\nis in the" +
		  " set of records:\n" + ppr(this.toString()));
    }
    rcd.normalize();
    if (this.names.length != rcd.names.length) {
      return false;
    }
    for (int i = 0; i < this.names.length; i++) {
      if ((!this.names[i].equals(rcd.names[i])) ||
	  (!this.values[i].member(rcd.values[i]))) {
	return false;
      }
    }
    return true;
  }

  public final boolean isFinite() {
    for (int i = 0; i < this.values.length; i++) {
      if (!this.values[i].isFinite()) return false;
    }
    return true;
  }
  
  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx < ex.path.length) {
      Assert.fail("Attempted to apply EXCEPT to the set of records:\n" +
		  ppr(this.toString()));
    }
    return ex.value;
  }

  public final Value takeExcept(ValueExcept[] exs) {
    if (exs.length != 0) {
      Assert.fail("Attempted to apply EXCEPT to the set of records:\n" +
		  ppr(this.toString()));
    }
    return this;
  }

  public final int size() {
    long sz = 1;
    for (int i = 0; i < this.values.length; i++) {
      sz *= this.values[i].size();
      if (sz < -2147483648 || sz > 2147483647) {
	Assert.fail(EC.TLC_MODULE_OVERFLOW, "the number of elements in:\n" +
		    ppr(this.toString()));
      }
    }
    return (int)sz;
  }

  public final boolean isNormalized() {
    if (this.rcdSet == null || this.rcdSet == DummyEnum) {
      for (int i = 0; i < this.names.length; i++) {
	if (!this.values[i].isNormalized()) {
	  return false;
	}
      }
      return true;
    }
    return this.rcdSet.isNormalized();
  }

  public final void normalize() {
    if (this.rcdSet == null || this.rcdSet == DummyEnum) {
      for (int i = 0; i < this.names.length; i++) {
	this.values[i].normalize();
      }
    }
    else {
      this.rcdSet.normalize();
    }
  }
  
  private final void sortByNames() {
    for (int i = 1; i < this.names.length; i++) {
      int cmp = this.names[0].compareTo(this.names[i]);
      if (cmp == 0) {
	Assert.fail("Field name " + this.names[0] + " occurs multiple times" +
		    " in set of records.");
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
    for (int i = 2; i < this.names.length; i++) {
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
	Assert.fail("Field name " + this.names[i] + " occurs multiple times" +
		    " in set of records.");
      }
      this.names[j] = st;
      this.values[j] = val;
    }
  }

  public final boolean isDefined() {
    boolean isDefined = true;
    for (int i = 0; i < this.values.length; i++) {
      isDefined = isDefined && this.values[i].isDefined();
    }
    return isDefined;
  }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    return this.equals(val);
  }
  
  /* The fingerprint  */
  public final long fingerPrint(long fp) {
    this.convertAndCache();
    return this.rcdSet.fingerPrint(fp);
  }

  public final Value permute(MVPerm perm) {
    this.convertAndCache();
    return this.rcdSet.permute(perm);
  }

  private final void convertAndCache() {
    if (this.rcdSet == null) {
      this.rcdSet = SetEnumValue.convert(this);
    }
    else if (this.rcdSet == DummyEnum) {
      SetEnumValue val = null;
      synchronized(this) {
	if (this.rcdSet == DummyEnum) {
	  val = SetEnumValue.convert(this);
	  val.deepNormalize();
	}
      }
      synchronized(this) {
	if (this.rcdSet == DummyEnum) { this.rcdSet = val; }
      }
    }
  }
      
  /* The string representation of the value. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    boolean unlazy = expand;
    try {
      if (unlazy) {
	long sz = 1;    
	for (int i = 0; i < this.values.length; i++) {
	  sz *= this.values[i].size();
	  if (sz < -2147483648 || sz > 2147483647) {
	    unlazy = false;
	    break;
	  }
	}
	unlazy = sz < TLCGlobals.enumBound;
      }
    }
    catch (Throwable e) { unlazy = false; }
    
    if (unlazy) {
      Value val = SetEnumValue.convert(this);
      return val.toString(sb, offset);
    }
    else {
      sb.append("[");
      int len = this.names.length;
      if (len != 0) {
	sb.append(names[0] + ": ");
	this.values[0].toString(sb, offset);
      }
      for (int i = 1; i < len; i++) {
	sb.append(", ");
	sb.append(names[i] + ": ");
	this.values[i].toString(sb, offset);
      }
      sb.append("]");
      return sb;
    }
  }

  public final ValueEnumeration elements() {
    if (this.rcdSet == null || this.rcdSet == DummyEnum) {
      return new Enumerator();
    }
    return this.rcdSet.elements();
  }

  final class Enumerator implements ValueEnumeration {
    private ValueEnumeration[] enums;
    private Value[] currentElems;
    private boolean isDone;

    public Enumerator() {
      this.enums = new ValueEnumeration[values.length];
      this.currentElems = new Value[values.length];
      this.isDone = false;
      for (int i = 0; i < values.length; i++) {
	if (values[i] instanceof Enumerable) {
	  this.enums[i] = ((Enumerable)values[i]).elements();
	  this.currentElems[i] = this.enums[i].nextElement();
	  if (this.currentElems[i] == null) {
	    this.enums = null;
	    this.isDone = true;
	    break;
	  }
	}
	else {
	  Assert.fail("Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn]," +
		      "\nbut can't enumerate the value of the `" + names[i] + "' field:\n" +
		      ppr(values[i].toString()));
	}
      }
    }

    public final void reset() {
      if (this.enums != null) {
	for (int i = 0; i < this.enums.length; i++) {
	  this.enums[i].reset();
	  this.currentElems[i] = this.enums[i].nextElement();
	}
	this.isDone = false;
      }
    }
    
    public final Value nextElement() {
      if (this.isDone) return null;
      Value[] elems = new Value[this.currentElems.length];
      for (int i = 0; i < elems.length; i++) {
	elems[i] = this.currentElems[i];
      }
      for (int i = elems.length-1; i >= 0; i--) {
	this.currentElems[i] = this.enums[i].nextElement();
	if (this.currentElems[i] != null) break;
	if (i == 0) {
	  this.isDone = true;
	  break;
	}
	this.enums[i].reset();
	this.currentElems[i] = this.enums[i].nextElement();
      }
      return new RecordValue(names, elems, true);
    }
    
  }

}
