// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:20:54 PST by lamport
//      modified on Thu Mar 11 21:25:20 PST 1999 by yuanyu

package tlc2.value;

public interface Enumerable {

  public int size();
  public boolean member(Value elem);
  public ValueEnumeration elements();

}

