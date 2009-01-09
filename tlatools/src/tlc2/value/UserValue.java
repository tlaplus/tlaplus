// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:09 PST by lamport
//      modified on Fri May 11 15:14:04 PDT 2001 by yuanyu

package tlc2.value;

import util.Assert;

public class UserValue extends Value {
  public UserObj userObj;

  public UserValue(UserObj obj) { this.userObj = obj; }

  public final byte getKind() { return USERVALUE; }

  public final int compareTo(Object obj) {
    if (obj instanceof UserValue) {
      return this.userObj.compareTo((Value)obj);
    }
    if (!(obj instanceof ModelValue))
      Assert.fail("Attempted to compare overridden value " + ppr(this.toString()) +
		  " with non-overridden value:\n" + ppr(obj.toString()));
    return 1;
  }
  
  public final boolean equals(Object obj) {
    return (this.compareTo(obj) == 0);
  }

  public final boolean member(Value val) {
    return this.userObj.member(val);
  }

  public final boolean isFinite() { return this.userObj.isFinite(); }
  
  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx < ex.path.length) {
      Assert.fail("Attempted to apply EXCEPT to the overridden value " +
		  ppr(this.toString()) + ".");
    }
    return ex.value;
  }

  public final Value takeExcept(ValueExcept[] exs) {
    if (exs.length != 0) {
      Assert.fail("Attempted to apply EXCEPT to the overridden value " +
		  ppr(this.toString()) + ".");
    }
    return this;
  }

  public final int size() {
    Assert.fail("Attempted to compute the number of elements in the overridden value " +
		ppr(this.toString()) + ".");
    return 0;   // make compiler happy
  }

  /* Nothing to normalize. */
  public final boolean isNormalized() { return true; }
  
  public final void normalize() { /*SKIP*/ }

  public final boolean isDefined() { return true; }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    return this.equals(val);
  }

  /* The string representation. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    return this.userObj.toString(sb, offset);
  }

}
