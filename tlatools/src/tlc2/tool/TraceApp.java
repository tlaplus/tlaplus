// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:42 PST by lamport
//      modified on Sat Feb 17 12:33:31 PST 2001 by yuanyu

package tlc2.tool;

public interface TraceApp {

  /* Reconstruct the initial state whose fingerprint is fp. */
  public TLCStateInfo getState(long fp);
  
  /* Reconstruct the next state of state s whose fingerprint is fp. */
  public TLCStateInfo getState(long fp, TLCState s);

  /* Reconstruct the info for the transition from s to s1. */
  public TLCStateInfo getState(TLCState s1, TLCState s);

}

