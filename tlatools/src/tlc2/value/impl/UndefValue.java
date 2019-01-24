// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Mon 30 Apr 2007 at 13:21:06 PST by lamport
//      modified on Tue Aug 15 23:08:23 PDT 2000 by yuanyu

package tlc2.value.impl;

import tlc2.tool.FingerprintException;
import tlc2.value.IValue;
import tlc2.value.ValueExcept;
import tlc2.value.Values;
import util.Assert;

public class UndefValue extends Value {

  public final static UndefValue ValUndef = new UndefValue();

public UndefValue() { /*SKIP*/ }

  public byte getKind() { return UNDEFVALUE; }

  public final int compareTo(Object obj) {
    try {
      return (obj instanceof UndefValue) ? 0 : 1;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      return (obj instanceof UndefValue);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean member(IValue elem) {
    try {
      Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
      "\nis an element " + Values.ppr(this.toString()));
      return false;    // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isFinite() {
    try {
      Assert.fail("Attempted to check if the value " + Values.ppr(this.toString()) +
      " is a finite set.");
      return false;    // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        Assert.fail("Attempted to apply EXCEPT construct to the value " +
        Values.ppr(this.toString()) + ".");
      }
      return ex.value;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue takeExcept(ValueExcept[] exs) {
    try {
      if (exs.length != 0) {
        Assert.fail("Attempted to apply EXCEPT construct to the value " +
        Values.ppr(this.toString()) + ".");
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int size() {
    try {
      Assert.fail("Attempted to compute the number of elements in the value " +
      Values.ppr(this.toString()) + ".");
      return 0;     // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isNormalized() { return true; }

  public final IValue normalize() { /*nop*/return this; }

  public final boolean isDefined() { return false; }

  public final IValue deepCopy() { return this; }

  public final boolean assignable(IValue val) { return true; }

  /* The string representation. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    try {
      return sb.append("UNDEF");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

}
