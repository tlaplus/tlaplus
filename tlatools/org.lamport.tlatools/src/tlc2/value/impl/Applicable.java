// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2023, Oracle and/or its affiliates.
// Last modified on Mon 30 Apr 2007 at 13:20:42 PST by lamport
//      modified on Wed Jun  2 00:10:22 PDT 1999 by yuanyu

package tlc2.value.impl;

import tlc2.tool.EvalException;
import tlc2.value.IValue;

/**
 * @deprecated
 *   This confused interface is implemented both by functions and operators, even though functions
 *   and operators are two very different TLA+ concepts that cannot be interchanged.  Clients of this
 *   interface should switch to either {@link FunctionValue} or {@link OpValue}, depending on the
 *   expected type of the object.  This one will be removed in the future.
 */
@Deprecated
public interface Applicable extends IValue {

  Value apply(Value[] args, int control) throws EvalException;
  Value apply(Value arg, int control) throws EvalException;
  Value getDomain() throws EvalException;
  Value select(Value arg) throws EvalException;

}
