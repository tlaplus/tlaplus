// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:03 PST by lamport
//      modified on Fri Aug 10 15:09:34 PDT 2001 by yuanyu

package tlc2.value;

import util.Assert;

public class SetDiffValue extends Value implements Enumerable {
  public Value set1;
  public Value set2;
  protected SetEnumValue diffSet; 
  
  /* Constructor */
  public SetDiffValue(Value set1, Value set2) {
    this.set1 = set1;
    this.set2 = set2;
    this.diffSet = null;
  }

  public final byte getKind() { return SETDIFFVALUE; }

  public final int compareTo(Object obj) {
    this.convertAndCache();
    return this.diffSet.compareTo(obj);
  }
  
  public final boolean equals(Object obj) {
    this.convertAndCache();
    return this.diffSet.equals(obj);
  }

  public final boolean member(Value elem) {
    return (this.set1.member(elem) && !this.set2.member(elem));
  }

  public final boolean isFinite() {
    if (this.set1.isFinite()) {
      return true;
    }
    if (!this.set2.isFinite()) {
      Assert.fail("Attempted to check if the set " + ppr(this.toString()) + "is finite.");
    }
    return false;
  }
  
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
    this.convertAndCache();
    return this.diffSet.size();
  }

  public final boolean isNormalized() {
    if (this.diffSet == null || this.diffSet == DummyEnum) {
      return this.set1.isNormalized();
    }
    return this.diffSet.isNormalized();
  }
  
  public final void normalize() {
    if (this.diffSet == null || this.diffSet == DummyEnum) {
      this.set1.normalize();
      this.set2.normalize();
    }
    else {
      this.diffSet.normalize();
    }
  }

  public final boolean isDefined() {
    return this.set1.isDefined() && this.set2.isDefined();
  }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    return this.equals(val);
  }

  /* The fingerprint methods */
  public final long fingerPrint(long fp) {
    this.convertAndCache();
    return this.diffSet.fingerPrint(fp);
  }

  public final Value permute(MVPerm perm) {
    this.convertAndCache();
    return this.diffSet.permute(perm);
  }

  private final void convertAndCache() {
    if (this.diffSet == null) {
      this.diffSet = SetEnumValue.convert(this);
    }
    else if (this.diffSet == DummyEnum) {
      SetEnumValue val = null;
      synchronized(this) {
	if (this.diffSet == DummyEnum) {
	  val = SetEnumValue.convert(this);
	  val.deepNormalize();
	}
      }
      synchronized(this) {
	if (this.diffSet == DummyEnum) { this.diffSet = val; }
      }
    }
  }

  /* The string representation  */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    try {
      if (expand) {
	Value val = SetEnumValue.convert(this);
	return val.toString(sb, offset);
      }
    }
    catch (Throwable e) { /*SKIP*/ }

    sb = this.set1.toString(sb, offset);
    sb = sb.append(" \\ ");
    sb = this.set2.toString(sb, offset);
    return sb;
  }

  public final ValueEnumeration elements() {
    if (this.diffSet == null || this.diffSet == DummyEnum) {
      return new Enumerator();
    }
    return this.diffSet.elements();
  }

  final class Enumerator implements ValueEnumeration {
    ValueEnumeration enum1;

    public Enumerator() {
      if (set1 instanceof Enumerable) {
	this.enum1 = ((Enumerable)set1).elements();
      }
      else {
	Assert.fail("Attempted to enumerate S \\ T when S:\n" +
		    ppr(set1.toString()) + "\nis not enumerable.");
      }
    }

    public final void reset() { this.enum1.reset(); }
    
    public final Value nextElement() {
      Value elem = this.enum1.nextElement();
      while (elem != null) {
	if (!set2.member(elem)) return elem;
	elem = this.enum1.nextElement();
      }
      return null;
    }
  }

}
