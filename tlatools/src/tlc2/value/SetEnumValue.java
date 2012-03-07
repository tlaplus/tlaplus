// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at 10:16:24 PST by lamport
//      modified on Mon Aug 20 10:54:08 PDT 2001 by yuanyu

package tlc2.value;

import tlc2.util.FP64;
import util.Assert;

public class SetEnumValue extends Value
implements Enumerable, Reducible {
  public ValueVec elems;         // the elements of the set
  private boolean isNorm;        // normalized?

  /* Constructor */
  public SetEnumValue(Value[] elems, boolean isNorm) {
    this.elems = new ValueVec(elems);
    this.isNorm = isNorm;
  }

  public SetEnumValue(ValueVec elems, boolean isNorm) {
    this.elems = elems;
    this.isNorm = isNorm;
  }

  public final byte getKind() { return SETENUMVALUE; }

  public final int compareTo(Object obj) {
    SetEnumValue set = convert(obj);
    if (set == null) {
      if (obj instanceof ModelValue) return 1;
      Assert.fail("Attempted to compare the set " + ppr(this.toString()) +
		  " with the value:\n" + ppr(obj.toString()));
    }
    this.normalize();
    set.normalize();
    int sz = this.elems.size();
    int cmp = sz - set.elems.size();
    if (cmp != 0) return cmp;
    for (int i = 0; i < sz; i++) {
      cmp = this.elems.elementAt(i).compareTo(set.elems.elementAt(i));
      if (cmp != 0) return cmp;
    }
    return 0;
  }
  
  public final boolean equals(Object obj) {
    SetEnumValue set = convert(obj);
    if (set == null) {
      if (obj instanceof ModelValue)  
         return ((ModelValue) obj).modelValueEquals(this) ;
      Assert.fail("Attempted to check equality of the set " + ppr(this.toString()) +
		  " with the value:\n" + ppr(obj.toString()));
    }
    this.normalize();
    set.normalize();
    int sz = this.elems.size();
    if (sz != set.elems.size()) {
      return false;
    }
    for (int i = 0; i < sz; i++) {
      if (!this.elems.elementAt(i).equals(set.elems.elementAt(i))) {
	return false;
      }
    }
    return true;
  }

  public final boolean member(Value elem) {
    return this.elems.search(elem, this.isNorm);
  }

  public final boolean isFinite() { return true; }
  
  public final Value diff(Value val) {
    int sz = this.elems.size();
    ValueVec diffElems = new ValueVec();
    for (int i = 0; i < sz; i++) {
      Value elem = this.elems.elementAt(i);
      if (!val.member(elem)) {
	diffElems.addElement(elem);
      }
    }
    return new SetEnumValue(diffElems, this.isNormalized());
  }

  public final Value cap(Value val) {
    int sz = this.elems.size();
    ValueVec capElems = new ValueVec();
    for (int i = 0; i < sz; i++) {
      Value elem = this.elems.elementAt(i);
      if (val.member(elem)) {
	capElems.addElement(elem);
      }
    }
    return new SetEnumValue(capElems, this.isNormalized());
  }

  public final Value cup(Value set) {
    int sz = this.elems.size();
    if (sz == 0) return set;

    if (set instanceof Reducible) {
      ValueVec cupElems = new ValueVec();
      for (int i = 0; i < sz; i++) {
	Value elem = this.elems.elementAt(i);
	cupElems.addElement(elem);
      }
      ValueEnumeration Enum = ((Enumerable)set).elements();
      Value elem;
      while ((elem = Enum.nextElement()) != null) {
	if (!this.member(elem)) cupElems.addElement(elem);
      }
      return new SetEnumValue(cupElems, false);
    }
    return new SetCupValue(this, set);
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
    this.normalize();
    return this.elems.size();
  }

  /* This method normalizes (destructively) this set. */
  public final boolean isNormalized() { return this.isNorm; }
  
  public final void normalize() {
    if (!this.isNorm) {
      this.elems.sort(true);   // duplicates eliminated
      this.isNorm = true;
    }
  }

  /* Convert val into a SetEnumValue.  Returns null if not possible. */
  public static final SetEnumValue convert(Object val) {
    switch (((Value)val).getKind()) {
    case SETENUMVALUE:
      return (SetEnumValue)val;
    case INTERVALVALUE:
      {
	IntervalValue intv = (IntervalValue)val;
	Value[] vals = new Value[intv.size()];
	for (int i = 0; i < vals.length; i++) {
	  vals[i] = IntValue.gen(i + intv.low);
	}
	return new SetEnumValue(vals, true);
      }
    case SETCAPVALUE:
      {
	SetCapValue cap = (SetCapValue)val;
	if (cap.capSet != null && cap.capSet != DummyEnum) {
	  return cap.capSet;
	}
	ValueVec vals = new ValueVec();
	ValueEnumeration Enum = cap.elements();	
	Value elem;
	while ((elem = Enum.nextElement()) != null) {
	  vals.addElement(elem);
	}
	return new SetEnumValue(vals, cap.isNormalized());
      }
    case SETCUPVALUE:
      {
	SetCupValue cup = (SetCupValue)val;
	if (cup.cupSet != null && cup.cupSet != DummyEnum) {
	  return cup.cupSet;
	}
	ValueVec vals = new ValueVec();
	ValueEnumeration Enum = cup.elements();
	Value elem;
	while ((elem = Enum.nextElement()) != null) {
	  vals.addElement(elem);
	}
	return new SetEnumValue(vals, false);
      }
    case SETDIFFVALUE:
      {
	SetDiffValue diff = (SetDiffValue)val;
	if (diff.diffSet != null && diff.diffSet != DummyEnum) {
	  return diff.diffSet;
	}
	ValueVec vals = new ValueVec();
	ValueEnumeration Enum = diff.elements();
	Value elem;
	while ((elem = Enum.nextElement()) != null) {
	  vals.addElement(elem);
	}
	return new SetEnumValue(vals, diff.set1.isNormalized());
      }
    case UNIONVALUE:
      {
	UnionValue uv = (UnionValue)val;
	if (uv.realSet != null && uv.realSet != DummyEnum) {
	  return uv.realSet;
	}
	ValueVec vals = new ValueVec();
	ValueEnumeration Enum = uv.elements();
	Value elem;
	while ((elem = Enum.nextElement()) != null) {
	  vals.addElement(elem);
	}
	return new SetEnumValue(vals, false);
      }
    case SUBSETVALUE:
      {
	SubsetValue pset = (SubsetValue)val;
	if (pset.pset != null && pset.pset != DummyEnum) {
	  return pset.pset;
	}
	ValueVec vals = new ValueVec(pset.size());
	ValueEnumeration Enum = pset.elements();
	Value elem;
	while ((elem = Enum.nextElement()) != null) {
	  vals.addElement(elem);
	}
	return new SetEnumValue(vals, false);
      }
    case SETOFRCDSVALUE:
      {
	SetOfRcdsValue rcds = (SetOfRcdsValue)val;
	if (rcds.rcdSet != null && rcds.rcdSet != DummyEnum) {
	  return rcds.rcdSet;
	}
	ValueVec vals = new ValueVec();
	ValueEnumeration Enum = rcds.elements();
	Value elem;
	while ((elem = Enum.nextElement()) != null) {
	  vals.addElement(elem);
	}
	return new SetEnumValue(vals, rcds.isNormalized());
      }
    case SETOFFCNSVALUE:
      {
	SetOfFcnsValue fcns = (SetOfFcnsValue)val;
	if (fcns.fcnSet != null && fcns.fcnSet != DummyEnum) {
	  return fcns.fcnSet;
	}
	ValueVec vals = new ValueVec();
	ValueEnumeration Enum = fcns.elements();
	Value elem;
	while ((elem = Enum.nextElement()) != null) {
	  vals.addElement(elem);
	}
	return new SetEnumValue(vals, fcns.isNormalized());
      }
    case SETOFTUPLESVALUE:
      {
	SetOfTuplesValue tvs = (SetOfTuplesValue)val;
	if (tvs.tupleSet != null && tvs.tupleSet != DummyEnum) {
	  return tvs.tupleSet;
	}
	ValueVec vals = new ValueVec();
	ValueEnumeration Enum = tvs.elements();
	Value elem;
	while ((elem = Enum.nextElement()) != null) {
	  vals.addElement(elem);
	}
	return new SetEnumValue(vals, tvs.isNormalized());
      }
    case SETPREDVALUE:
      {
	SetPredValue sPred = (SetPredValue)val;
	if (sPred.tool == null) return (SetEnumValue)sPred.inVal;
	ValueVec vals = new ValueVec();
	ValueEnumeration Enum = sPred.elements();
	Value elem;
	while ((elem = Enum.nextElement()) != null) {
	  vals.addElement(elem);
	}
	return new SetEnumValue(vals, sPred.isNormalized());
      }
    default:
      // null if val can not be converted.
      return null;
    }
  }
  
  public final boolean isDefined() {
    boolean defined = true;
    int sz = this.elems.size();    
    for (int i = 0; i < sz; i++) {
      defined = defined && this.elems.elementAt(i).isDefined();
    }
    return defined;
  }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) { return this.equals(val); }

  /* The fingerprint methods */
  public final long fingerPrint(long fp) {
    this.normalize();
    int sz = this.elems.size();    
    fp = FP64.Extend(fp, SETENUMVALUE);
    fp = FP64.Extend(fp, sz);
    for (int i = 0; i < sz; i++) {
      Value elem = this.elems.elementAt(i);
      fp = elem.fingerPrint(fp);
    }
    return fp;
  }

  public final Value permute(MVPerm perm) {
    int sz = this.elems.size();
    Value[] vals = new Value[sz];
    boolean changed = false;
    for (int i = 0; i < sz; i++) {
      vals[i] = this.elems.elementAt(i).permute(perm);
      changed = (changed || vals[i] != this.elems.elementAt(i));
    }
    if (changed) {
      return new SetEnumValue(vals, false);
    }
    return this;
  }

  /* The string representation */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    // If this SetEnumValue object is created by a union, at least one of
    // whose elements is a Cartesian product, then this can be an unnormalized
    // set with repeated elements.  It would therefore seem like a good idea to
    // normalize this object here.  Since this toString method is probably
    // used only for printing the value, it seems that correcting this should
    // not do any harm.  Therefore, LL added the following if statement
    // on 5 Mar 2012.
    if (!this.isNormalized()) {
        this.normalize();
    }
    
    int len = this.elems.size();
    sb = sb.append("{");
    if (len > 0) {
      this.elems.elementAt(0).toString(sb, offset);
    }
    for (int i = 1; i < len; i++) {
      sb.append(", ");
      this.elems.elementAt(i).toString(sb, offset);
    }
    sb.append("}");
    return sb;
  }

  public final ValueEnumeration elements() { return new Enumerator(); }
  
  final class Enumerator implements ValueEnumeration {
    int index = 0;

    public Enumerator() {
      normalize();
    }
    
    public final void reset() { this.index = 0; }

    public final Value nextElement() {
      if (this.index < elems.size()) {
	return elems.elementAt(this.index++);
      }
      return null;
    }
  }
  
}
