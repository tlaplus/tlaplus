// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at 10:18:39 PST by lamport
//      modified on Fri Aug 10 15:09:59 PDT 2001 by yuanyu

package tlc2.value;

import tlc2.TLCGlobals;
import util.Assert;

public class SetOfTuplesValue extends Value implements Enumerable {
  public Value[] sets;
  protected SetEnumValue tupleSet;
  
  /* Constructor */
  public SetOfTuplesValue(Value[] sets) {
    this.sets = sets;
    this.tupleSet = null;
  }

  public SetOfTuplesValue(Value val) {
    this.sets = new Value[1];
    this.sets[0] = val;
    this.tupleSet = null;
  }

  public SetOfTuplesValue(Value v1, Value v2) {
    this.sets = new Value[2];
    this.sets[0] = v1;
    this.sets[1] = v2;
    this.tupleSet = null;
  }

  public final byte getKind() { return SETOFTUPLESVALUE; }

  public final int compareTo(Object obj) {
    this.convertAndCache();
    return this.tupleSet.compareTo(obj);    
  }
  
  public final boolean equals(Object obj) {
    if (obj instanceof SetOfTuplesValue) {
      SetOfTuplesValue tvs = (SetOfTuplesValue)obj;
      if (this.sets.length != tvs.sets.length) {
	return false;
      }
      for (int i = 0; i < this.sets.length; i++) {
	if (!this.sets[i].equals(tvs.sets[i])) {
	  return false;
	}
      }
      return true;
    }
    this.convertAndCache();
    return this.tupleSet.equals(obj);
  }

  public final boolean member(Value elem) {
    TupleValue tv = TupleValue.convert(elem);
    if (tv == null) {
      FcnRcdValue fcn = FcnRcdValue.convert(elem);
      if (fcn == null) {
	if (elem instanceof ModelValue)    
          return ((ModelValue) elem).modelValueMember(this) ;
	Assert.fail("Attempted to check if non-tuple\n" + ppr(elem.toString()) +
		    "\nis in the set of tuples:\n" + ppr(this.toString()));
      }
      if (fcn.intv != null) return false;
      for (int i = 0; i < fcn.domain.length; i++) {
	if (!(fcn.domain[i] instanceof IntValue)) {
	  Assert.fail("Attempted to check if non-tuple\n" + ppr(elem.toString()) +
		      "\nis in the set of tuples:\n" + ppr(this.toString()));
	}
      }
      return false;
    }
    if (tv.elems.length == this.sets.length) {
      for (int i = 0; i < this.sets.length; i++) {
	if (!this.sets[i].member(tv.elems[i]))
	  return false;
      }
      return true;
    }
    return false;
  }

  public final boolean isFinite() {
    for (int i = 0; i < this.sets.length; i++) {
      if (!this.sets[i].isFinite()) {
	return false;
      }
    }
    return true;
  }
  
  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx < ex.path.length) {
      Assert.fail("Attempted to apply EXCEPT construct to the set of tuples:\n" +
		  ppr(this.toString()));
    }
    return ex.value;
  }

  public final Value takeExcept(ValueExcept[] exs) {
    if (exs.length != 0) {
      Assert.fail("Attempted to apply EXCEPT construct to the set of tuples:\n" +
		  ppr(this.toString()));
    }
    return this;
  }

  public final int size() {
    long sz = 1;
    for (int i = 0; i < this.sets.length; i++) {
      sz *= this.sets[i].size();
      if (sz < -2147483648 || sz > 2147483647) {
	Assert.fail("Overflow when computing the number of elements in " +
		    ppr(this.toString()));
      }
    }
    return (int)sz;
  }

  public final boolean isNormalized() {
    if (this.tupleSet == null || this.tupleSet == DummyEnum) {
      for (int i = 0; i < this.sets.length; i++) {
	if (!this.sets[i].isNormalized()) {
	  return false;
	}
      }
      return true;
    }
    return this.tupleSet.isNormalized();
  }

  public final void normalize() {
    if (this.tupleSet == null || this.tupleSet == DummyEnum) {
      for (int i = 0; i < this.sets.length; i++) {
	this.sets[i].normalize();
      }
    }
    else {
      this.tupleSet.normalize();
    }
  }

  public final boolean isDefined() {
    boolean defined = true;
    for (int i = 0; i < this.sets.length; i++) {
      defined = defined && this.sets[i].isDefined();
    }
    return defined;
  }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    return this.equals(val);
  }

  /* The fingerprint  */
  public final long fingerPrint(long fp) {
    this.convertAndCache();
    return this.tupleSet.fingerPrint(fp);
  }
  
  public final Value permute(MVPerm perm) {
    this.convertAndCache();
    return this.tupleSet.permute(perm);
  }

  private final void convertAndCache() {
    if (this.tupleSet == null) {
      this.tupleSet = SetEnumValue.convert(this);
    }
    else if (this.tupleSet == DummyEnum) {
      SetEnumValue val = null;
      synchronized(this) {
	if (this.tupleSet == DummyEnum) {
	  val = SetEnumValue.convert(this);
	  val.deepNormalize();
	}
      }
      synchronized(this) {
	if (this.tupleSet == DummyEnum) { this.tupleSet = val; }
      }
    }
  }
      
  /* The string representation of the value. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    boolean unlazy = expand;
    try {
      if (unlazy) {
	long sz = 1;    
	for (int i = 0; i < this.sets.length; i++) {
	  sz *= this.sets[i].size();
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
      if (this.sets.length > 0) {
	sb.append("(");
	this.sets[0].toString(sb, offset);
      }
      for (int i = 1; i < this.sets.length; i++) {
	sb.append(" X ");
	this.sets[i].toString(sb, offset);
      }
      if (this.sets.length > 0) {
	sb.append(")");
      }
      return sb;
    }
  }
  
  public final ValueEnumeration elements() {
    if (this.tupleSet == null || this.tupleSet == DummyEnum) {
      return new Enumerator();
    }
    return this.tupleSet.elements();
  }

  final class Enumerator implements ValueEnumeration {
    private ValueEnumeration[] enums;
    private Value[] currentElems;
    private boolean isDone;
    
    public Enumerator() {
      this.enums = new ValueEnumeration[sets.length];
      this.currentElems = new Value[sets.length];
      this.isDone = false;
      for (int i = 0; i < sets.length; i++) {
	if (sets[i] instanceof Enumerable) {
	  this.enums[i] = ((Enumerable)sets[i]).elements();
	  this.currentElems[i] = this.enums[i].nextElement();
	  if (this.currentElems[i] == null) {
	    this.enums = null;
	    this.isDone = true;
	    break;
	  }
	}
	else {
	  Assert.fail("Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn," +
		      "\nbut can't enumerate s" + i + ":\n" + ppr(sets[i].toString()));
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
      return new TupleValue(elems);
    }
  }

}
