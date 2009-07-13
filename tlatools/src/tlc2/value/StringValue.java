// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at 10:19:41 PST by lamport
//      modified on Fri Aug 10 15:06:37 PDT 2001 by yuanyu

package tlc2.value;

import tlc2.util.FP64;
import util.Assert;
import util.UniqueString;

public class StringValue extends Value {
  public UniqueString val; 

  /* Constructor */
  public StringValue(String str) {
    // SZ 11.04.2009: changed the access method to equivalent
    this.val = UniqueString.uniqueStringOf(str);
  }

  public StringValue(UniqueString var) {
    this.val = var;
  }
  
  public final byte getKind() { return STRINGVALUE; }

  public final UniqueString getVal() { return this.val; }

  public final int compareTo(Object obj) {
    if (obj instanceof StringValue) {
      return this.val.compareTo(((StringValue)obj).val);
    }
    if (!(obj instanceof ModelValue)) {
      Assert.fail("Attempted to compare string " + ppr(this.toString()) +
		  " with non-string:\n" + ppr(obj.toString()));
    }
    return 1;
  }

  public final boolean equals(Object obj) {
    if (obj instanceof StringValue) {
      return this.val.equals(((StringValue)obj).getVal());
    }
    if (!(obj instanceof ModelValue)) {
      Assert.fail("Attempted to check equality of string " + ppr(this.toString()) +
		  " with non-string:\n" + ppr(obj.toString()));
    }
    return ((ModelValue) obj).modelValueEquals(this) ;
  }

  public final boolean member(Value elem) {
    Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
		"\nis an element of the string " + ppr(this.toString()));
    return false;     // make compiler happy
  }

  public final boolean isFinite() {
    Assert.fail("Attempted to check if the string " + ppr(this.toString()) +
		" is a finite set.");
    return false;     // make compiler happy
  }
  
  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx < ex.path.length) {
      Assert.fail("Attempted to apply EXCEPT construct to the string " +
		  ppr(this.toString()) + ".");
    }
    return ex.value;
  }

  public final Value takeExcept(ValueExcept[] exs) {
    if (exs.length != 0) {
      Assert.fail("Attempted to apply EXCEPT construct to the string " +
		  ppr(this.toString()) + ".");
    }
    return this;
  }

  public final int size() {
    Assert.fail("Attempted to compute the number of elements in the string " +
		ppr(this.toString()) + ".");
    return 0;       // make compiler happy
  }

  public final boolean isNormalized() { return true; }

  public final void normalize() { /*SKIP*/ }

  public final boolean isDefined() { return true; }

  public final Value deepCopy() { return this; }

  public final boolean assignable(Value val) {
    return ((val instanceof StringValue) &&
	    this.equals(val));
  }

  public final int length() { return this.val.length(); }
  
  /* The fingerprint method */
  public final long fingerPrint(long fp) {
    fp = FP64.Extend(fp, STRINGVALUE) ;
    fp = FP64.Extend(fp, this.val.length()) ;
    fp = FP64.Extend(fp, this.val.toString());
    return fp;
  }

  public final Value permute(MVPerm perm) { return this; }

  /*************************************************************************
  * toString() modified 23 Aug 2007 by LL to call PrintVersion so strings  *
  * with special characters are printed properly.                          *
  *************************************************************************/
  final String PrintVersion(String str) {
    StringBuffer buf = new StringBuffer(str.length()) ;
    for (int i = 0 ; i < str.length() ; i++) {
      switch (str.charAt(i)) {
        case '\"' :
          buf.append("\\\"") ;
          break ;
        case '\\' :
          buf.append("\\\\") ;
          break ;
        case '\t' :
          buf.append("\\t") ;
          break ;
        case '\n' :
          buf.append("\\n") ;
          break ;
        case '\f' :
          buf.append("\\f") ;
          break ;
        case '\r' :
          buf.append("\\r") ;
          break ;
        default :
          buf.append(str.charAt(i)) ;
          break ;
       } // switch
     }; // for
    return buf.toString();
   }


  /* The string representation of the value. */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    return sb.append("\"" + PrintVersion(this.val.toString()) + "\"");
  }

}
