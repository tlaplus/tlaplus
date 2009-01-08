// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:19:03 PST by lamport
//      modified on Thu Dec  7 13:47:27 PST 2000 by yuanyu

package tlc2.module;

import tlc2.value.*;
import tlc2.tool.*;

public class AnySet extends UserObj {

  private static Value AnySet = new UserValue(new AnySet());

  public static Value ANY() { return AnySet; }

  public final int compareTo(Value val) {
    String msg = "Attempted to compare ANY with the value\n" + Value.ppr(val.toString());
    throw new EvalException(msg);
  }

  public final boolean member(Value val) { return true; }

  public final boolean isFinite() { return false; }
  
  public final StringBuffer toString(StringBuffer sb, int offset) {
    return sb.append("ANY");
  }
}
