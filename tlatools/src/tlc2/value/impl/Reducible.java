// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:02 PST by lamport
//      modified on Tue Mar 23 00:37:35 PST 1999 by yuanyu

package tlc2.value.impl;

import tlc2.value.IValue;
import tlc2.value.ValueEnumeration;

public interface Reducible {

  public int size();
  public boolean member(IValue elem);
  public IValue diff(IValue val);
  public IValue cap(IValue val);
  public IValue cup(IValue val);

  public ValueEnumeration elements();
}

