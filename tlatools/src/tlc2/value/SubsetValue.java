// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:46:07 PST by lamport
//      modified on Fri Aug 10 15:10:16 PDT 2001 by yuanyu

package tlc2.value;

import java.util.BitSet;

import tlc2.output.EC;
import util.Assert;

public class SubsetValue extends Value implements Enumerable {
  public Value set;           // SUBSET set
  protected SetEnumValue pset;

  /* Constructor */
  public SubsetValue(Value set) {
    this.set = set;
    this.pset = null;
  }

  public final byte getKind() { return SUBSETVALUE; }

  public final int compareTo(Object obj) {
    if (obj instanceof SubsetValue) {
      return this.set.compareTo(((SubsetValue)obj).set);
    }
    this.convertAndCache();
    return this.pset.compareTo(obj);    
  }
  
  public final boolean equals(Object obj) {
    if (obj instanceof SubsetValue) {
      return this.set.equals(((SubsetValue)obj).set);
    }
    this.convertAndCache();
    return this.pset.equals(obj);
  }

  public final boolean member(Value val) {
    if (val instanceof Enumerable) {
      ValueEnumeration Enum = ((Enumerable)val).elements();
      Value elem;
      while ((elem = Enum.nextElement()) != null) {
	if (!this.set.member(elem)) return false;
      }
    }
    else {
      Assert.fail("Attempted to check if the non-enumerable value\n" +
		  ppr(val.toString()) + "\nis element of\n" + ppr(this.toString()));
    }
    return true;    
  }

  public final boolean isFinite() { return this.set.isFinite(); }
  
  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx < ex.path.length) {
      Assert.fail("Attempted to apply EXCEPT to the set " + ppr(this.toString()) + ".");
    }
    return ex.value;
  }

  public final Value takeExcept(ValueExcept[] exs) {
    if (exs.length != 0) {
      Assert.fail("Attempted to apply EXCEPT to the set " + ppr(this.toString()) + ".");
    }
    return this;
  }

  public final int size() {
    int sz = this.set.size();
    if (sz >= 31) {
      Assert.fail(EC.TLC_MODULE_OVERFLOW, "the number of elements in:\n" +
		  ppr(this.toString()));
    }
    return (1 << sz);
  }

  public final boolean isNormalized() {
    return (this.pset != null &&
	    this.pset != DummyEnum &&
	    this.pset.isNormalized());
  }
  
  public final void normalize() {
    if (this.pset == null || this.pset == DummyEnum) {
      this.set.normalize();
    }
    else {
      this.pset.normalize();
    }
  }

  public final boolean isDefined() { return this.set.isDefined(); }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) { return this.equals(val); }

  /* The fingerprint  */
  public final long fingerPrint(long fp) {
    this.convertAndCache();
    return this.pset.fingerPrint(fp);
  }

  public final Value permute(MVPerm perm) {
    this.convertAndCache();
    return this.pset.permute(perm);
  }

  private final void convertAndCache() {
    if (this.pset == null) {
      this.pset = SetEnumValue.convert(this);
    }
    else if (this.pset == DummyEnum) {
      SetEnumValue val = null;
      synchronized(this) {
	if (this.pset == DummyEnum) {
	  val = SetEnumValue.convert(this);
	  val.deepNormalize();
	}
      }
      synchronized(this) {
	if (this.pset == DummyEnum) { this.pset = val; }
      }
    }
  }
  
  /* The string representation  */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    boolean unlazy = expand;
    try {
      if (unlazy) {
	unlazy = this.set.size() < 7;
      }
    }
    catch (Throwable e) { unlazy = false; }

    if (unlazy) {
      Value val = SetEnumValue.convert(this);
      return val.toString(sb, offset);
    }
    else {
      sb = sb.append("SUBSET ");
      sb = this.set.toString(sb, offset);
      return sb;
    }
  }

  public final ValueEnumeration elements() {
    if (this.pset == null || this.pset == DummyEnum) {
      return new Enumerator();
    }
    return this.pset.elements();
  }

  final class Enumerator implements ValueEnumeration {
    ValueVec elems;
    private BitSet descriptor;
    
    public Enumerator() {
      set = SetEnumValue.convert(set);
      set.normalize();
      this.elems = ((SetEnumValue)set).elems;
      this.descriptor = new BitSet(this.elems.size());
    }

    public final void reset() {
      this.descriptor = new BitSet(this.elems.size());
    }
    
    public final Value nextElement() {
      if (this.descriptor == null) return null;
      ValueVec vals = new ValueVec();
      int sz = this.elems.size();
      if (sz == 0) {
	this.descriptor = null;
      }
      else {
	for (int i = 0; i < sz; i++) {
	  if (this.descriptor.get(i)) {
	    vals.addElement(this.elems.elementAt(i));
	  }
	}
	for (int i = 0; i < sz; i++) {
	  if (this.descriptor.get(i)) {
	    this.descriptor.clear(i);
	    if (i >= sz - 1) {
	      this.descriptor = null;
	      break;
	    }
	  }
	  else {
	    this.descriptor.set(i);
	    break;
	  }
	}
      }
      return new SetEnumValue(vals, true);
    }
    
  }
  
}
