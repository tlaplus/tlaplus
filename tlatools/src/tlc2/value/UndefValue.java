// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:06 PST by lamport
//      modified on Tue Aug 15 23:08:23 PDT 2000 by yuanyu

package tlc2.value;

import util.Assert;

public class UndefValue extends Value {

  public UndefValue() { /*SKIP*/ }

  public byte getKind() { return UNDEFVALUE; }

  public final int compareTo(Object obj) {
    return (obj instanceof UndefValue) ? 0 : 1;
  }
  
  public final boolean equals(Object obj) {
    return (obj instanceof UndefValue);
  }

  public final boolean member(Value elem) {
    Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
		"\nis an element " + ppr(this.toString()));
    return false;    // make compiler happy
  }

  public final boolean isFinite() {
    Assert.fail("Attempted to check if the value " + ppr(this.toString()) +
		" is a finite set.");
    return false;    // make compiler happy
  }

  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx < ex.path.length) {
      Assert.fail("Attempted to apply EXCEPT construct to the value " +
		  ppr(this.toString()) + ".");
    }
    return ex.value;
  }
  
  public final Value takeExcept(ValueExcept[] exs) {
    if (exs.length != 0) {
      Assert.fail("Attempted to apply EXCEPT construct to the value " +
		  ppr(this.toString()) + ".");
    }
    return this;
  }

  public final int size() {
    Assert.fail("Attempted to compute the number of elements in the value " +
		ppr(this.toString()) + ".");
    return 0;     // make compiler happy
  }

  public final boolean isNormalized() { return true; }

  public final void normalize() { /*nop*/ }

  public final boolean isDefined() { return false; }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) { return true; }

  /* The string representation. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    return sb.append("UNDEF");
  }

}
