// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:08 PST by lamport
//      modified on Thu Feb  8 21:23:55 PST 2001 by yuanyu

package tlc2.value;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import tla2sany.semantic.SemanticNode;
import tlc2.util.Context;
import util.Assert;

public class LazyValue extends Value {
  /**
   * The field val is the result of evaluating expr in context con and
   * a pair of states.  If val is null, then the value has not been
   * computed, but when computed, the value can be cached in the field
   * val. If val is ValUndef, then the value has not been computed,
   * and when computed, it can not be cached in the field val.
   */

  public SemanticNode expr;
  public Context con;
  public Value val;

  public LazyValue(SemanticNode expr, Context con) {
    this.expr = expr;
    this.con = con;
    this.val = null;
  }

  public final void setUncachable() { this.val = ValUndef; }

  public final byte getKind() { return LAZYVALUE; }

  public final int compareTo(Object obj) {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to compare lazy values.");
    }
    return this.val.compareTo(obj);
  }
  
  public final boolean equals(Object obj) {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to check equality of lazy values.");
    }
    return this.val.equals(obj);
  }

  public final boolean member(Value elem) {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to check set membership of lazy values.");
    }
    return this.val.member(elem);
  }

  public final boolean isFinite() {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to check if a lazy value is a finite set.");
    }
    return this.val.isFinite();
  }
  
  public final Value takeExcept(ValueExcept ex) {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to apply EXCEPT construct to lazy value.");
    }
    return this.val.takeExcept(ex);
  }

  public final Value takeExcept(ValueExcept[] exs) {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to apply EXCEPT construct to lazy value.");
    }
    return this.val.takeExcept(exs);
  }

  public final int size() {
    if (this.val == null || this.val == ValUndef) {
       Assert.fail("Error(TLC): Attempted to compute size of lazy value.");
    }
    return this.val.size();
  }

  private void readObject(ObjectInputStream ois)
  throws IOException, ClassNotFoundException {
    this.val = (Value)ois.readObject();
  }

  private void writeObject(ObjectOutputStream oos) throws IOException {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to serialize lazy value.");
    }
    oos.writeObject(this.val);
  }
  
  /* Nothing to normalize. */
  public final boolean isNormalized() {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to normalize lazy value.");
    }
    return this.val.isNormalized();
  }
  
  public final void normalize() {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to normalize lazy value.");
    }
    this.val.normalize();
  }

  public final boolean isDefined() { return true; }

  public final Value deepCopy() {
    if (this.val == null || this.val == ValUndef) return this;
    return this.val.deepCopy();
  }

  public final boolean assignable(Value val) {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to call assignable on lazy value.");
    }
    return this.val.assignable(val);
  }

  /* The fingerprint method */
  public final long fingerPrint(long fp) {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to fingerprint a lazy value.");
    }
    return this.val.fingerPrint(fp);
  }

  public final Value permute(MVPerm perm) {
    if (this.val == null || this.val == ValUndef) {
      Assert.fail("Error(TLC): Attempted to apply permutation to lazy value.");
    }
    return this.val.permute(perm);
  }

  /* The string representation of the value. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    if (this.val == null || this.val == ValUndef) {
      return sb.append("<LAZY " + this.expr + ">");
    }
    return this.val.toString(sb, offset);
  }

}
