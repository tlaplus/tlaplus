// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:34 PST by lamport
//      modified on Mon Jan  8 23:35:23 PST 2001 by yuanyu

package tlc2.tool.distributed;

import tlc2.tool.distributed.fp.FPSetRMI;
import tlc2.tool.distributed.fp.IFPSetManager;

import java.io.IOException;
import java.rmi.Remote;
import java.rmi.RemoteException;

/**
 * @version $Id$
 */
public interface TLCServerRMI extends Remote {
    void registerWorker(TLCWorkerRMI worker)
            throws IOException;

    void registerFPSet(FPSetRMI fpSet, String hostname) throws RemoteException;

    Boolean getCheckDeadlock() throws RemoteException;

    Boolean getPreprocess() throws RemoteException;

    IFPSetManager getFPSetManager() throws RemoteException;

    long getIrredPolyForFP() throws RemoteException;

    /**
     * @return true iff server is done computing states
     */
    boolean isDone() throws RemoteException;

    /**
     * @return The name and (potentially) path to the specification file
     */
    String getSpecFileName() throws RemoteException;

    /**
     * @return The name and (potentially) path to the configuration file
     */
    String getConfigFileName() throws RemoteException;

    /**
     * Reads the given file from the server stripping the path the just the file name.
     *
     * @param file A full qualified or relative (to server spec dir) file name.
     * @return the file requested
     */
    byte[] getFile(final String file) throws RemoteException;
}
