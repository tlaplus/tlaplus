// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Sat 23 February 2008 at 10:01:16 PST by lamport
//      modified on Fri Aug 10 15:07:07 PDT 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IBoolValue;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;

public class BoolValue extends Value implements IBoolValue {
  public boolean val;   // the boolean
  public static final BoolValue ValFalse = new BoolValue(false);
  /* Value constants. */
  public static final BoolValue ValTrue  = new BoolValue(true);

  /* Constructor */
  public BoolValue(boolean b) { this.val = b; }

  @Override
  public final boolean getVal() {
	  return val;
  }
  
  @Override
  public final byte getKind() { return BOOLVALUE; }

  @Override
  public final int compareTo(Object obj) {
    try {
      if (obj instanceof BoolValue) {
        int x = this.val ? 1 : 0;
        int y = ((BoolValue)obj).val ? 1 : 0;
        return x - y;
      }
      if (!(obj instanceof ModelValue)) {
        Assert.fail("Attempted to compare boolean " + Values.ppr(this.toString()) +
        " with non-boolean:\n" + Values.ppr(obj.toString()), getSource());
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
      if (obj instanceof BoolValue) {
        return this.val == ((BoolValue)obj).val;
      }
      if (!(obj instanceof ModelValue)) {
        Assert.fail("Attempted to compare equality of boolean " + Values.ppr(this.toString()) +
        " with non-boolean:\n" + Values.ppr(obj.toString()), getSource());
      }
      return ((ModelValue) obj).modelValueEquals(this) ;
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
      "\nis an element of the boolean " + Values.ppr(this.toString()), getSource());
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final boolean isFinite() {
    try {
      Assert.fail("Attempted to check if the boolean " + Values.ppr(this.toString()) +
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
        Assert.fail("Attempted to apply EXCEPT construct to the boolean " +
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
        Assert.fail("Attempted to apply EXCEPT construct to the boolean " +
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
      Assert.fail("Attempted to compute the number of elements in the boolean " +
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
	  return false;
  }

  @Override
  public final boolean isNormalized() { return true; }

  @Override
  public final Value normalize() { /*nop*/ return this; }

  @Override
  public final boolean isDefined() { return true; }

  @Override
  public final IValue deepCopy() { return this; }

  @Override
  public final boolean assignable(Value val) {
    try {
      return ((val instanceof BoolValue) &&
        this.val == ((BoolValue)val).val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	@Override
	public void write(IValueOutputStream vos) throws IOException {
		vos.writeByte(BOOLVALUE);
		vos.writeBoolean(val);
	}

  /* The fingerprint method */
  @Override
  public final long fingerPrint(long fp) {
    try {
      fp = FP64.Extend(fp, BOOLVALUE) ;
      fp = FP64.Extend(fp, (this.val) ? 't' : 'f') ;
      return fp;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final IValue permute(IMVPerm perm) { return this; }

  /* The string representation */
  public final StringBuffer toString(StringBuffer sb, int offset) {
	return toString(sb, offset, true);
}

/* The string representation */
  @Override
  public final StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
    try {
      return sb.append((this.val) ? "TRUE" : "FALSE");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

}
