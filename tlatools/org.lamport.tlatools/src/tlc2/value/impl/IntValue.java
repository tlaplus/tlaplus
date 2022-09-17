// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:08:05 PST by lamport
//      modified on Fri Aug 10 15:07:30 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;

public class IntValue extends Value {
  private static final IntValue[] cache;

  static {
    cache = new IntValue[10];
    for (int i = 0; i < cache.length; i++) {
      cache[i] = new IntValue(i);
    }
  }

	public static final IntValue ValNegOne = gen(-1);
	
	public static final IntValue ValOne    = gen(1);
	
	public static final IntValue ValZero   = gen(0);

  public static final int nbits(int tmp) {
    int nb = 0;
    while(tmp != 0 && tmp != -1) {
      nb++;
      tmp >>= 1;
    }
    return nb + 1;
  }
  
  public static IntValue sum(IntValue n, IntValue m) {
	  return IntValue.gen(n.val + m.val);
  }

  public final int val;

  private IntValue(int i) { this.val = i; }

  @Override
  public final byte getKind() { return INTVALUE; }

  // the number of bits needed to encode the value of this int
  public final int nbits() {
    try {
      return nbits(this.val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public static IntValue gen(int i) {
    if (i >= 0 && i < cache.length) {
      return cache[i];
    }
    return new IntValue(i);
  }

  @Override
  public final int compareTo(Object obj) {
    try {
      if (obj instanceof IntValue) {
        return Integer.compare(this.val, ((IntValue)obj).val);
      }
      if (!(obj instanceof ModelValue)) {
        Assert.fail("Attempted to compare integer " + Values.ppr(this.toString()) +
        " with non-integer:\n" + Values.ppr(obj.toString()), getSource());
      }
      return ((ModelValue) obj).modelValueCompareTo(this);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      if (obj instanceof IntValue) {
        return this.val == ((IntValue)obj).val;
      }
      if (!(obj instanceof ModelValue)) {
        Assert.fail("Attempted to check equality of integer " + Values.ppr(this.toString()) +
        " with non-integer:\n" + Values.ppr(obj.toString()), getSource());
      }
      return ((ModelValue) obj).modelValueEquals(this);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean member(Value elem) {
    try {
      Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
      "\nis an element of the integer " + Values.ppr(this.toString()), getSource());
      return false;  // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() {
    try {
      Assert.fail("Attempted to check if the integer " + Values.ppr(this.toString()) +
      " is a finite set.", getSource());
      return false;   // make compiler happy
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
        Assert.fail("Attempted to appy EXCEPT construct to the integer " +
        Values.ppr(this.toString()) + ".", getSource());
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
        Assert.fail("Attempted to apply EXCEPT construct to the integer " +
        Values.ppr(this.toString()) + ".", getSource());
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
      Assert.fail("Attempted to compute the number of elements in the integer " +
      Values.ppr(this.toString()) + ".", getSource());
      return 0;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public boolean mutates() {
	  // finalized after construction.
	  return false;
  }

  @Override
  public final boolean isNormalized() { return true; }

  @Override
  public final Value normalize() { /*nop*/return this; }

  @Override
  public final boolean isDefined() { return true; }

  @Override
  public final IValue deepCopy() { return this; }

  @Override
  public final boolean assignable(Value val) {
    try {
      return ((val instanceof IntValue) &&
        this.val == ((IntValue)val).val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	@Override
	public void write(IValueOutputStream vos) throws IOException {
		vos.writeByte(INTVALUE);
		vos.writeInt(val);
	}

  /* The fingerprint methods */
  @Override
  public final long fingerPrint(long fp) {
    try {
      return FP64.Extend(FP64.Extend(fp, INTVALUE), this.val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue permute(IMVPerm perm) { return this; }

  /* The string representation. */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean ignored) {
    try {
      return sb.append(this.val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

}
