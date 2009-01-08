// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at  9:58:18 PST by lamport
//      modified on Thu Dec  7 13:47:27 PST 2000 by yuanyu

package tlc2.module;

import tlc2.value.*;
import tlc2.tool.*;

public class Strings extends UserObj {

  private static Value SetString = new UserValue(new Strings());

  public static Value STRING() { return SetString; }

  public final int compareTo(Value val) {
    if ((val instanceof UserValue) &&
	(((UserValue)val).userObj instanceof Strings)) {
      return 0;
    }
    if (val instanceof ModelValue) return 1;
    String msg = "Attempted to compare STRING with the value\n" +
      Value.ppr(val.toString());
    throw new EvalException(msg);
  }

  public final boolean member(Value val) {
    if (val instanceof StringValue) return true;
    if (val instanceof ModelValue)  
      return ((ModelValue) val).modelValueMember(this) ;
    String msg = "Attempted to check if the value:\n" + Value.ppr(val.toString()) +
      "\nis an element of STRING.";
    throw new EvalException(msg);
  }

  public final boolean isFinite() { return false; }
  
  public final StringBuffer toString(StringBuffer sb, int offset) {
    return sb.append("STRING");
  }
}
