// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:06 PST by lamport
//      modified on Tue Aug 15 23:08:23 PDT 2000 by yuanyu

package tlc2.value;

import tlc2.tool.ModelChecker;
import tlc2.tool.FingerprintException;
import util.Assert;

public class UndefValue extends Value {

  public UndefValue() { /*SKIP*/ }

  public byte getKind() { return UNDEFVALUE; }

  public final int compareTo(Object obj) {
    try {
      return (obj instanceof UndefValue) ? 0 : 1;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      return (obj instanceof UndefValue);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean member(Value elem) {
    try {
      Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
      "\nis an element " + ppr(this.toString()));
      return false;    // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isFinite() {
    try {
      Assert.fail("Attempted to check if the value " + ppr(this.toString()) +
      " is a finite set.");
      return false;    // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        Assert.fail("Attempted to apply EXCEPT construct to the value " +
        ppr(this.toString()) + ".");
      }
      return ex.value;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value takeExcept(ValueExcept[] exs) {
    try {
      if (exs.length != 0) {
        Assert.fail("Attempted to apply EXCEPT construct to the value " +
        ppr(this.toString()) + ".");
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int size() {
    try {
      Assert.fail("Attempted to compute the number of elements in the value " +
      ppr(this.toString()) + ".");
      return 0;     // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isNormalized() { return true; }

  public final void normalize() { /*nop*/ }

  public final boolean isDefined() { return false; }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) { return true; }

  /* The string representation. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    try {
      return sb.append("UNDEF");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

}
