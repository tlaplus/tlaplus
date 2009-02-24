// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at 10:17:11 PST by lamport
//      modified on Fri Aug 10 15:09:46 PDT 2001 by yuanyu

package tlc2.value;

import tlc2.TLCGlobals;
import util.Assert;

public class SetOfFcnsValue extends Value implements Enumerable {
  public Value domain;        /* Function domain  */
  public Value range;         /* Function range   */
  protected SetEnumValue fcnSet;
  
  /* Constructor */
  public SetOfFcnsValue(Value domain, Value range) {
    this.domain = domain;
    this.range = range;
    this.fcnSet = null;
  }

  public final byte getKind() { return SETOFFCNSVALUE; }

  public final int compareTo(Object obj) {
    this.convertAndCache();
    return this.fcnSet.compareTo(obj);
  }
  
  public final boolean equals(Object obj) {
    if (obj instanceof SetOfFcnsValue) {
      SetOfFcnsValue fcns = (SetOfFcnsValue)obj;
      return (this.domain.equals(fcns.domain) &&
	      this.range.equals(fcns.range));
    }
    this.convertAndCache();
    return this.fcnSet.equals(obj);
  }

  public final boolean member(Value elem) {
    FcnRcdValue fcn = FcnRcdValue.convert(elem);
    if (fcn == null) {
      if (elem instanceof ModelValue)  
         return ((ModelValue) elem).modelValueMember(this) ;
      Assert.fail("Attempted to check if \n" + elem + "\nwhich is not a TLC function" +
		  " value, is in the set of functions:\n" + ppr(this.toString()));
    }
    if (fcn.intv == null) {
      fcn.normalize();
      Value fdom = new SetEnumValue(fcn.domain, true);
      if (this.domain.equals(fdom)) {
	for (int i = 0; i < fcn.values.length; i++) {
	  if (!this.range.member(fcn.values[i])) {
	    return false;
	  }
	}
	return true;
      }
    }
    else {
      if (fcn.intv.equals(this.domain)) {
	for (int i = 0; i < fcn.values.length; i++) {
	  if (!this.range.member(fcn.values[i])) return false;
	}
	return true;
      }
    }
    return false;
  }

  public final boolean isFinite() {
    return this.domain.isFinite() && this.range.isFinite();
  }
  
  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx < ex.path.length) {
      Assert.fail("Attempted to apply EXCEPT to the set of functions:\n" +
		  ppr(this.toString()));
    }
    return ex.value;
  }

  public final Value takeExcept(ValueExcept[] exs) {
    if (exs.length != 0) {
      Assert.fail("Attempted to apply EXCEPT to the set of functions:\n" +
		  ppr(this.toString()));
    }
    return this;
  }

  public final int size() {
    int dsz = this.domain.size();
    int rsz = this.range.size();
    long sz = 1;    
    for (int i = 0; i < dsz; i++) {
      sz *= rsz;
      if (sz < -2147483648 || sz > 2147483647) {
	Assert.fail("Overflow when computing the number of elements in:\n" +
		    ppr(toString()));
      }
    }
    return (int)sz;
  }

  public final boolean isNormalized() {
    if (this.fcnSet == null || this.fcnSet == DummyEnum) { 
      return this.domain.isNormalized() && this.range.isNormalized();
    }
    return this.fcnSet.isNormalized();
  }
  
  public final void normalize() {
    if (this.fcnSet == null || this.fcnSet == DummyEnum) {
      this.domain.normalize();
      this.range.normalize();
    }
    else {
      this.fcnSet.normalize();
    }
  }

  public final boolean isDefined() {
    return this.domain.isDefined() && this.range.isDefined();
  }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    return this.equals(val);
  }

  /* The fingerprint  */
  public final long fingerPrint(long fp) {
    this.convertAndCache();
    return this.fcnSet.fingerPrint(fp);
  }

  public final Value permute(MVPerm perm) {
    this.convertAndCache();
    return this.fcnSet.permute(perm);
  }

  private final void convertAndCache() {
    if (this.fcnSet == null) {
      this.fcnSet = SetEnumValue.convert(this);
    }
    else if (this.fcnSet == DummyEnum) {
      SetEnumValue val = null;
      synchronized(this) {
	if (this.fcnSet == DummyEnum) {
	  val = SetEnumValue.convert(this);
	  val.deepNormalize();
	}
      }
      synchronized(this) {
	if (this.fcnSet == DummyEnum) { this.fcnSet = val; }
      }
    }
  }
  
  /* The string representation of the value. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    boolean unlazy = expand;
    try {
      if (unlazy) {
	int dsz = this.domain.size();
	int rsz = this.range.size();
	long sz = 1;    
	for (int i = 0; i < dsz; i++) {
	  sz *= rsz;
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
      this.domain.toString(sb, offset);
      sb.append(" -> ");
      this.range.toString(sb, offset);
      sb.append("]");
      return sb;
    }
  }
    
  public final ValueEnumeration elements() {
    if (this.fcnSet == null || this.fcnSet == DummyEnum) {
      return new Enumerator();
    }
    return this.fcnSet.elements();    
  }

  final class Enumerator implements ValueEnumeration {
    private Value[] dom;
    private ValueEnumeration[] enums;
    private Value[] currentElems;
    private boolean isDone;
    
    public Enumerator() {
      this.isDone = false;
      SetEnumValue domSet = SetEnumValue.convert(domain);
      if (domSet == null)
	Assert.fail("Attempted to enumerate a set of the form [D -> R]," +
		    "but the domain D:\n" + ppr(domain.toString()) +
		    "\ncannot be enumerated.");
      domSet.normalize();
      ValueVec elems = domSet.elems;
      int sz = elems.size();
      if (range instanceof Enumerable) {
	this.dom = new Value[sz];
	this.enums = new ValueEnumeration[sz];
	this.currentElems = new Value[sz];
	// SZ Feb 24, 2009: never read locally
	// ValueEnumeration enumeration = ((Enumerable)domSet).elements();
	for (int i = 0; i < sz; i++) {
	  this.dom[i] = elems.elementAt(i);
	  this.enums[i] = ((Enumerable)range).elements();
	  this.currentElems[i] = this.enums[i].nextElement();
	  if (this.currentElems[i] == null) {
	    this.enums = null;
	    this.isDone = true;
	    break;
	  }
	}
      }
      else {
	Assert.fail("Attempted to enumerate a set of the form [D -> R]," +
		    "but the range R:\n" + ppr(range.toString()) +
		    "\ncannot be enumerated.");
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
      if (elems.length == 0) {
	this.isDone = true;
      }
      else {
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
      }
      return new FcnRcdValue(this.dom, elems, true);
    }
    
  }

}
