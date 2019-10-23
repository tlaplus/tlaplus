// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:02 PST by lamport
//      modified on Tue Mar 23 00:37:35 PST 1999 by yuanyu

package tlc2.value.impl;

public interface Reducible {

  int size();
  boolean member(Value elem);
  Value diff(Value val);
  Value cap(Value val);
  Value cup(Value val);

  ValueEnumeration elements();
}

