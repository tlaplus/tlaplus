// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:46:50 PST by lamport
//      modified on Fri Aug 10 15:10:39 PDT 2001 by yuanyu

package tlc2.value;

import util.Assert;

public class UnionValue extends Value implements Enumerable {
  public Value set;
  protected SetEnumValue realSet;
  
  /* Constructor */
  public UnionValue(Value set) {
    this.set = set;
    this.realSet = null;
  }

  public byte getKind() { return UNIONVALUE; }

  public final int compareTo(Object obj) {
    this.convertAndCache();
    return this.realSet.compareTo(obj);
  }
  
  public final boolean equals(Object obj) {
    this.convertAndCache();
    return this.realSet.equals(obj);
  }

  public final boolean member(Value elem) {
    if (!(this.set instanceof Enumerable)) {
      Assert.fail("Attempted to check if:\n " + ppr(elem.toString()) +
		  "\nis an element of the non-enumerable set:\n " +
		  ppr(this.toString()));
    }
    ValueEnumeration Enum = ((Enumerable)this.set).elements();
    Value val;
    while ((val = Enum.nextElement()) != null) {
      if (val.member(elem)) return true;
    }
    return false;
  }

  public final boolean isFinite() {
    if (!(this.set instanceof Enumerable)) {
      Assert.fail("Attempted to check if the nonenumerable set:\n" + ppr(this.toString()) +
		  "\nis a finite set.");
    }
    ValueEnumeration Enum = ((Enumerable)this.set).elements();
    Value val;
    while ((val = Enum.nextElement()) != null) {
      if (!val.isFinite()) return false;
    }
    return true;
  }
  
  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx < ex.path.length) {
      Assert.fail("Attempted to apply EXCEPT to the set:\n" + ppr(this.toString()));
    }
    return ex.value;
  }

  public final Value takeExcept(ValueExcept[] exs) {
    if (exs.length != 0) {
      Assert.fail("Attempted to apply EXCEPT to the set:\n " + ppr(this.toString()) + ".");
    }
    return this;
  }

  public final int size() {
    this.convertAndCache();
    return this.realSet.size();
  }

  public final boolean isNormalized() {
    return (this.realSet != null &&
	    this.realSet != DummyEnum &&
	    this.realSet.isNormalized());
  }    
  
  public final void normalize() {
    if (this.realSet != null && this.realSet != DummyEnum) {
      this.realSet.normalize();
    }
  }

  public final boolean isDefined() { return this.set.isDefined(); }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    return this.equals(val);
  }

  public static Value union(Value val) {
    boolean canCombine = (val instanceof SetEnumValue);
    if (canCombine) {
      ValueVec elems = ((SetEnumValue)val).elems;
      for (int i = 0; i < elems.size(); i++) {
	canCombine = (canCombine &&
		      (elems.elementAt(i) instanceof SetEnumValue));
      }
      if (canCombine) {
	ValueVec resElems = new ValueVec();
	Value result = new SetEnumValue(resElems, false);
	for (int i = 0; i < elems.size(); i++) {
	  ValueVec elems1 = ((SetEnumValue)elems.elementAt(i)).elems;
	  for (int j = 0; j < elems1.size(); j++) {
	    Value elem = elems1.elementAt(j);
	    if (!result.member(elem)) resElems.addElement(elem);
	  }
	}
	return result;
      }
    }
    return new UnionValue(val);
  }

  /* The fingerprint  */
  public final long fingerPrint(long fp) {
    this.convertAndCache();    
    return this.realSet.fingerPrint(fp);
  }

  public final Value permute(MVPerm perm) {
    this.convertAndCache();
    return this.realSet.permute(perm);
  }

  private final void convertAndCache() {
    if (this.realSet == null) {
      this.realSet = SetEnumValue.convert(this);
    }
    else if (this.realSet == DummyEnum) {
      SetEnumValue val = null;
      synchronized(this) {
	if (this.realSet == DummyEnum) {
	  val = SetEnumValue.convert(this);
	  val.deepNormalize();
	}
      }
      synchronized(this) {
	if (this.realSet == DummyEnum) { this.realSet = val; }
      }
    }
  }
  
  /* String representation of this value. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    if (expand) {
      Value val = SetEnumValue.convert(this);
      return val.toString(sb, offset);
    }
    else {
      sb = sb.append("UNION(");
      sb = this.set.toString(sb, offset);
      sb.append(")");
      return sb;
    }
  }

  public final ValueEnumeration elements() {
    if (this.realSet == null || this.realSet == DummyEnum) {
      return new Enumerator();
    }
    return this.realSet.elements();
  }
  
  final class Enumerator implements ValueEnumeration {
    ValueEnumeration Enum;
    Value elemSet;
    ValueEnumeration elemSetEnum;
    
    public Enumerator() {
      if (!(set instanceof Enumerable)) {
	Assert.fail("Attempted to enumerate the nonenumerable set:\n"+
		    ppr(this.toString()));
      }
      this.Enum = ((Enumerable)set).elements();
      this.elemSet = this.Enum.nextElement();
      if (this.elemSet != null) {
	if (!(this.elemSet instanceof Enumerable)) {
	  Assert.fail("Attempted to enumerate UNION(s), but some element of s is nonenumerable.");
	}
	this.elemSetEnum = ((Enumerable)this.elemSet).elements();
      }
    }

    public final void reset() {
      this.Enum.reset();
      this.elemSet = this.Enum.nextElement();
      this.elemSetEnum = ((Enumerable)this.elemSet).elements();
    }

    public final Value nextElement() {
      if (this.elemSet == null) return null;
      Value val = this.elemSetEnum.nextElement();
      if (val == null) {
	this.elemSet = this.Enum.nextElement();
	if (this.elemSet == null) return null;
	if (!(this.elemSet instanceof Enumerable)) {
	  Assert.fail("Attempted to enumerate the nonenumerable set:\n" +
		      ppr(this.elemSet.toString()) +
		      "\nwhen enumerating:\n" + ppr(this.toString()));
	}
	this.elemSetEnum = ((Enumerable)this.elemSet).elements();
	val = this.nextElement();
      }
      return val;
    }
    
  }

}
