// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at 10:12:59 PST by lamport
//      modified on Fri Aug 10 15:07:36 PDT 2001 by yuanyu

package tlc2.value;

import tlc2.util.FP64;
import util.Assert;

public class IntervalValue extends Value
implements Enumerable, Reducible {
  public int low, high;   // the integer interval [low, high]

  /* Constructor */
  public IntervalValue(int low, int high) {
    this.low = low;
    this.high = high;
  }

  public final byte getKind() { return INTERVALVALUE; }

  public final int compareTo(Object obj) {
    if (obj instanceof IntervalValue) {
      IntervalValue intv = (IntervalValue)obj;
      int cmp = this.size() - intv.size();
      if (cmp != 0) return cmp;
      if (this.size() == 0) return 0;
      return this.low - intv.low;
    }
    // Well, we have to convert them to sets and compare.
    return SetEnumValue.convert(this).compareTo(obj);
  }

  public final boolean equals(Object obj) {
    if (obj instanceof IntervalValue) {
      IntervalValue intv = (IntervalValue)obj;
      if (this.size() == 0) return intv.size() == 0;
      return (this.low == intv.low) && (this.high == intv.high);
    }
    // Well, we have to convert them to sets and compare.
    return SetEnumValue.convert(this).equals(obj);
  }
  
  public final boolean member(Value elem) {
    if (elem instanceof IntValue) {
      int x = ((IntValue)elem).val;
      return (x >= low) && (x <= high);
    }
    if (   (this.low <= this.high) 
         && (   !(elem instanceof ModelValue)
             || (((ModelValue) elem).type != 0)) ) {
      Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
		  "\nis in the integer interval " + ppr(this.toString()));
    }
    return false;
  }

  public final boolean isFinite() { return true; }

  public final int size() {
    if (this.high < this.low) return 0;
    return this.high - this.low + 1;
  }

  /* Return this - val.  */
  public final Value diff(Value val) {
    ValueVec diffElems = new ValueVec();
    for (int i = this.low; i <= this.high; i++) {
      Value elem = IntValue.gen(i);      
      if (!val.member(elem)) diffElems.addElement(elem);
    }
    return new SetEnumValue(diffElems, true);
  }

  /* Return this \cap val. */
  public final Value cap(Value val) {
    ValueVec capElems = new ValueVec();
    for (int i = this.low; i <= this.high; i++) {
      Value elem = IntValue.gen(i);
      if (val.member(elem)) capElems.addElement(elem);
    }
    return new SetEnumValue(capElems, true);
  }

  /* Return this \cup val.  */
  public final Value cup(Value set) {
    if (this.size() == 0) return set;

    if (set instanceof Reducible) {
      ValueVec cupElems = new ValueVec();
      for (int i = this.low; i <= this.high; i++) {
	cupElems.addElement(IntValue.gen(i));
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
      Assert.fail("Attempted to apply EXCEPT construct to the interval value " +
		  ppr(this.toString()) + ".");
    }
    return ex.value;
  }

  public final Value takeExcept(ValueExcept[] exs) {
    if (exs.length != 0) {
      Assert.fail("Attempted to apply EXCEPT construct to the interval value " +
		  ppr(this.toString()) + ".");
    }
    return this;
  }

  public final boolean isNormalized() { return true; }
  
  public final void normalize() { /*nop*/ }

  public final boolean isDefined() { return true; }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    return ((val instanceof IntervalValue) &&
	    this.high == ((IntervalValue)val).high &&
	    this.low == ((IntervalValue)val).low);
  }

  /* The fingerprint method */
  public final long fingerPrint(long fp) {
    fp = FP64.Extend(fp, SETENUMVALUE);
    fp = FP64.Extend(fp, this.size()) ;
    for (int i = this.low; i <= this.high; i++) {
      fp = FP64.Extend(fp, INTVALUE);
      fp = FP64.Extend(fp, i);
    }
    return fp;
  }

  public final Value permute(MVPerm perm) {
    return this;
  }
  
  /* The string representation */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    if (this.low <= this.high) {
      return sb.append(this.low).append("..").append(this.high);
    }
    return sb.append("{").append("}");
  }

  public final ValueEnumeration elements() {
    return new Enumerator();
  }
  
  final class Enumerator implements ValueEnumeration {
    int index = low;

    public final void reset() { this.index = low; }

    public final Value nextElement() {
      if (this.index <= high) {
	return IntValue.gen(this.index++);
      }
      return null;
    }
    
  }
  
}
