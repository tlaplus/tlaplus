// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:02 PST by lamport
//      modified on Tue Mar 23 00:37:35 PST 1999 by yuanyu

package tlc2.value;

public interface Reducible {

  public int size();
  public boolean member(Value elem);
  public Value diff(Value val);
  public Value cap(Value val);
  public Value cup(Value val);

  public ValueEnumeration elements();
}

