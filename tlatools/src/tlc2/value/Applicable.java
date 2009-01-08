// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:20:42 PST by lamport
//      modified on Wed Jun  2 00:10:22 PDT 1999 by yuanyu

package tlc2.value;

import tlc2.tool.EvalException;

public interface Applicable {
  
  public Value apply(Value[] args, int control) throws EvalException;
  public Value apply(Value arg, int control) throws EvalException;
  public Value getDomain() throws EvalException;
  public Value select(Value arg) throws EvalException;
  
}
