// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at 10:01:16 PST by lamport
//      modified on Fri Aug 10 15:07:07 PDT 2001 by yuanyu

package tlc2.value;

import tlc2.tool.ModelChecker;
import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import util.Assert;

public class BoolValue extends Value {
  public boolean val;   // the boolean

  /* Constructor */
  public BoolValue(boolean b) { this.val = b; }

  public final byte getKind() { return BOOLVALUE; }

  public final int compareTo(Object obj) {
    try {
      if (obj instanceof BoolValue) {
        int x = this.val ? 1 : 0;
        int y = ((BoolValue)obj).val ? 1 : 0;
        return x - y;
      }
      if (!(obj instanceof ModelValue)) {
        Assert.fail("Attempted to compare boolean " + ppr(this.toString()) +
        " with non-boolean:\n" + ppr(obj.toString()));
      }
      return 1;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      if (obj instanceof BoolValue) {
        return this.val == ((BoolValue)obj).val;
      }
      if (!(obj instanceof ModelValue)) {
        Assert.fail("Attempted to compare equality of boolean " + ppr(this.toString()) +
        " with non-boolean:\n" + ppr(obj.toString()));
      }
      return ((ModelValue) obj).modelValueEquals(this) ;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean member(Value elem) {
    try {
      Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
      "\nis an element of the boolean " + ppr(this.toString()));
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isFinite() {
    try {
      Assert.fail("Attempted to check if the boolean " + ppr(this.toString()) +
      " is a finite set.");
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value takeExcept(ValueExcept ex) {
    try {
      if (ex.idx < ex.path.length) {
        Assert.fail("Attempted to apply EXCEPT construct to the boolean " +
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
        Assert.fail("Attempted to apply EXCEPT construct to the boolean " +
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
      Assert.fail("Attempted to compute the number of elements in the boolean " +
      ppr(this.toString()) + ".");
      return 0;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isNormalized() { return true; }

  public final void normalize() { /*nop*/ }

  public final boolean isDefined() { return true; }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    try {
      return ((val instanceof BoolValue) &&
        this.val == ((BoolValue)val).val);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The fingerprint method */
  public final long fingerPrint(long fp) {
    try {
      fp = FP64.Extend(fp, BOOLVALUE) ;
      fp = FP64.Extend(fp, (this.val) ? 't' : 'f') ;
      return fp;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final Value permute(MVPerm perm) { return this; }

  /* The string representation */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    try {
      return sb.append((this.val) ? "TRUE" : "FALSE");
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (ModelChecker.isFingerprintStackOn) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

}
