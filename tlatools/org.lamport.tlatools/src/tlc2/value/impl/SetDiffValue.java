// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2021, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:21:03 PST by lamport
//      modified on Fri Aug 10 15:09:34 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;

import tlc2.TLCGlobals;
import tlc2.tool.FingerprintException;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;

public class SetDiffValue extends EnumerableValue implements Enumerable {
  public final Value set1;
  public final Value set2;
  protected SetEnumValue diffSet;

  /* Constructor */
  public SetDiffValue(Value set1, Value set2) {
    this.set1 = set1;
    this.set2 = set2;
    this.diffSet = null;
  }

  @Override
  public final byte getKind() { return SETDIFFVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {
      this.convertAndCache();
      return this.diffSet.compareTo(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      this.convertAndCache();
      return this.diffSet.equals(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean member(Value elem) {
    try {
      return (this.set1.member(elem) && !this.set2.member(elem));
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() {
    try {
      if (this.set1.isFinite()) {
        return true;
      }
      if (!this.set2.isFinite()) {
        Assert.fail("Attempted to check if the set " + Values.ppr(this.toString()) + "is finite.", getSource());
      }
      return false;
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
      return this.diffSet.size();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isNormalized() {
    try {
      if (this.diffSet == null || this.diffSet == SetEnumValue.DummyEnum) {
        return this.set1.isNormalized();
      }
      return this.diffSet.isNormalized();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final Value normalize() {
    try {
      if (this.diffSet == null || this.diffSet == SetEnumValue.DummyEnum) {
        this.set1.normalize();
        this.set2.normalize();
      }
      else {
        this.diffSet.normalize();
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
      if (diffSet == null) {
        diffSet = SetEnumValue.DummyEnum;
      }
      else if (diffSet != SetEnumValue.DummyEnum) {
        diffSet.deepNormalize();
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
		diffSet.write(vos);
	}

  /* The fingerprint methods */
  @Override
  public final long fingerPrint(long fp) {
    try {
      this.convertAndCache();
      return this.diffSet.fingerPrint(fp);
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
      return this.diffSet.permute(perm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private final void convertAndCache() {
    if (this.diffSet == null) {
      this.diffSet = (SetEnumValue) this.toSetEnum();
    }
    else if (this.diffSet == SetEnumValue.DummyEnum) {
      SetEnumValue val = (SetEnumValue) this.toSetEnum();
      val.deepNormalize();
      this.diffSet = val;
    }
  }

  @Override
  public final Value toSetEnum() {
      if (this.diffSet != null && this.diffSet != SetEnumValue.DummyEnum) {
        return this.diffSet;
      }
      ValueVec vals = new ValueVec();
      ValueEnumeration Enum = this.elements();
      Value elem;
      while ((elem = Enum.nextElement()) != null) {
        vals.addElement(elem);
      }
      if (coverage) {cm.incSecondary(vals.size());}
      return new SetEnumValue(vals, this.set1.isNormalized(), cm);
  }

  /* The string representation  */
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
      sb = sb.append(" \\ ");
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
      if (this.diffSet == null || this.diffSet == SetEnumValue.DummyEnum) {
        return new Enumerator();
      }
      return this.diffSet.elements();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }

  }

  final class Enumerator implements ValueEnumeration {
    ValueEnumeration enum1;

    public Enumerator() {
      if (set1 instanceof Enumerable) {
        this.enum1 = ((Enumerable)set1).elements();
      }
      else {
        Assert.fail("Attempted to enumerate S \\ T when S:\n" +
              Values.ppr(set1.toString()) + "\nis not enumerable.", getSource());
      }
    }

    @Override
    public final void reset() { this.enum1.reset(); }

    @Override
    public final Value nextElement() {
    	Value elem = this.enum1.nextElement();
      while (elem != null) {
    	  if (coverage) { cm.incSecondary(); }
        if (!set2.member(elem)) return elem;
        elem = this.enum1.nextElement();
      }
      return null;
    }
  }

}
