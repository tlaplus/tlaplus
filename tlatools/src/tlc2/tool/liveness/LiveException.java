// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:44 PST by lamport
//      modified on Tue Jun 13 17:16:21 PDT 2000 by yuanyu

package tlc2.tool.liveness;

public class LiveException extends RuntimeException {

  public LiveException() { super(); }

  public LiveException(String msg) { super(msg); }
}
