// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:41 PST by lamport
//      modified on Mon Jan  1 23:05:27 PST 2001 by yuanyu

package tlc2.tool;

import java.io.IOException;
import java.rmi.Remote;
import java.rmi.RemoteException;

public interface TLCWorkerRMI extends Remote {

  public Object[] getNextStates(TLCState[] states)
    throws RemoteException, WorkerException;

  public void exit() throws IOException;
  
}
