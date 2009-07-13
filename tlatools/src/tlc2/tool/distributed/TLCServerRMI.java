// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:34 PST by lamport
//      modified on Mon Jan  8 23:35:23 PST 2001 by yuanyu

package tlc2.tool.distributed;

import java.io.IOException;
import java.rmi.Remote;
import java.rmi.RemoteException;


/**
 * @deprecated not used currently
 * @version $Id$
 */
public interface TLCServerRMI extends Remote {
  public void registerWorker(TLCWorkerRMI worker, String hostname)
    throws IOException;

  public String getAppName() throws RemoteException;
  public Boolean getCheckDeadlock() throws RemoteException;
  public Boolean getPreprocess() throws RemoteException;  
  public FPSetManager getFPSetManager() throws RemoteException;
  public long getIrredPolyForFP() throws RemoteException;
}
