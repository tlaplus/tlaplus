// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2021, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:21:03 PST by lamport
//      modified on Fri Aug 10 15:09:28 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;

import tlc2.TLCGlobals;
import tlc2.tool.FingerprintException;
import tlc2.tool.coverage.CostModel;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;

public class SetCupValue extends EnumerableValue implements Enumerable {
  public final Value set1;
  public final Value set2;
  protected SetEnumValue cupSet;

  /* Constructor */
  public SetCupValue(Value set1, Value set2) {
    this.set1 = set1;
    this.set2 = set2;
    this.cupSet = null;
  }

  public SetCupValue(Value set1, Value set2, CostModel cm) {
	this(set1, set2);
	this.cm = cm;
  }

  @Override
  public final byte getKind() { return SETCUPVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {
      this.convertAndCache();
      return this.cupSet.compareTo(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      this.convertAndCache();
      return this.cupSet.equals(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean member(Value elem) {
    try {
      return this.set1.member(elem) || this.set2.member(elem);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() {
    try {
      return this.set1.isFinite() && this.set2.isFinite();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        Assert.fail("Attempted to apply EXCEPT to the set " + Values.ppr(this.toString()) + ".", getSource());
      }
      return ex.value;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value takeExcept(ValueExcept[] exs) {
    try {
      if (exs.length != 0) {
        Assert.fail("Attempted to apply EXCEPT to the set " + Values.ppr(this.toString()) + ".", getSource());
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final int size() {
    try {
      this.convertAndCache();
      return this.cupSet.size();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isNormalized() {
    try {
      return (this.cupSet != null &&
        this.cupSet != SetEnumValue.DummyEnum &&
        this.cupSet.isNormalized());
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value normalize() {
    try {
      if (this.cupSet != null && this.cupSet != SetEnumValue.DummyEnum) {
        this.cupSet.normalize();
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final void deepNormalize() {
	    try {
      set1.deepNormalize();
      set2.deepNormalize();
      if (cupSet == null) {
        cupSet = SetEnumValue.DummyEnum;
      }
      else if (cupSet != SetEnumValue.DummyEnum) {
        cupSet.deepNormalize();
      }
	    }
	    catch (RuntimeException | OutOfMemoryError e) {
	      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	      else { throw e; }
	    }
  }
  
  @Override
  public final boolean isDefined() {
    try {
      return this.set1.isDefined() && this.set2.isDefined();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue deepCopy() { return this; }

  @Override
  public final boolean assignable(Value val) {
    try {
      return this.equals(val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	@Override
	public final void write(final IValueOutputStream vos) throws IOException {
		cupSet.write(vos);
	}

  /* The fingerprint methods */
  @Override
  public final long fingerPrint(long fp) {
    try {
      this.convertAndCache();
      return this.cupSet.fingerPrint(fp);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue permute(IMVPerm perm) {
    try {
      this.convertAndCache();
      return this.cupSet.permute(perm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private final void convertAndCache() {
    if (this.cupSet == null) {
      this.cupSet = (SetEnumValue) this.toSetEnum();
    }
    else if (this.cupSet == SetEnumValue.DummyEnum) {
      SetEnumValue val = (SetEnumValue) this.toSetEnum();
      val.deepNormalize();
      this.cupSet = val;
    }
  }

  @Override
  public final Value toSetEnum() {
      if (this.cupSet != null && this.cupSet != SetEnumValue.DummyEnum) {
        return this.cupSet;
      }
      ValueVec vals = new ValueVec();
      ValueEnumeration Enum = this.elements();
      Value elem;
      while ((elem = Enum.nextElement()) != null) {
        vals.addElement(elem);
      }
      if (coverage) {cm.incSecondary(vals.size());}
      return new SetEnumValue(vals, false, cm);
  }

  /* String representation of the value. */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
    try {
      try {
        if (TLCGlobals.expand) {
          Value val = this.toSetEnum();
          return val.toString(sb, offset, swallow);
        }
      }
      catch (Throwable e) { if (!swallow) throw e; }

      sb = this.set1.toString(sb, offset, swallow);
      sb = sb.append(" \\cup ");
      sb = this.set2.toString(sb, offset, swallow);
      return sb;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final ValueEnumeration elements() {
    try {
      if (this.cupSet == null || this.cupSet == SetEnumValue.DummyEnum) {
        return new Enumerator();
      }
      return this.cupSet.elements();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }

  }

  final class Enumerator implements ValueEnumeration {
    ValueEnumeration enum1;
    ValueEnumeration enum2;

    public Enumerator() {
      if ((set1 instanceof Enumerable) &&
          (set2 instanceof Enumerable)) {
        this.enum1 = ((Enumerable)set1).elements();
        this.enum2 = ((Enumerable)set2).elements();
      }
      else {
        Assert.fail("Attempted to enumerate S \\cup T when S:\n" +
              Values.ppr(set1.toString()) + "\nand T:\n" + Values.ppr(set2.toString()) +
              "\nare not both enumerable", getSource());
      }
    }

    @Override
    public final void reset() {
      this.enum1.reset();
      this.enum2.reset();
    }

    @Override
    public final Value nextElement() {
  	  if (coverage) { cm.incSecondary(); }
  	Value elem = this.enum1.nextElement();
      if (elem != null) return elem;
      elem = this.enum2.nextElement();
      return elem;
    }
  }

}
