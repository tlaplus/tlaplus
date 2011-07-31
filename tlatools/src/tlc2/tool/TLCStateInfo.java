// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:35 PST by lamport 
//      modified on Sat Feb 17 12:07:55 PST 2001 by yuanyu 

package tlc2.tool;

public class TLCStateInfo {
  public TLCStateInfo predecessorState;
  public long stateNumber;
  public TLCState state;
  public Object info;

  public TLCStateInfo(TLCState s, Object info) {
    this.state = s;
    this.info = info;
  }

  public final long fingerPrint() {
    return this.state.fingerPrint();
  }

  public final String toString() {
    return this.state.toString();
  }
}
