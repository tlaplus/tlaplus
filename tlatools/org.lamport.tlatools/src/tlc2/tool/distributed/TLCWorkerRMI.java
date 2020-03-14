// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:41 PST by lamport
//      modified on Mon Jan  1 23:05:27 PST 2001 by yuanyu

package tlc2.tool.distributed;

import java.net.URI;
import java.rmi.Remote;
import java.rmi.RemoteException;

import tlc2.tool.TLCState;
import tlc2.tool.WorkerException;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface TLCWorkerRMI extends Remote {

	/**
	 * @param states The initial states to work with
	 * @return The next states for the initial state wet
	 * @throws RemoteException
	 * @throws WorkerException
	 */
	public NextStateResult getNextStates(TLCState[] states) throws RemoteException,
			WorkerException;
	
	/**
	 * @return true iff worker is still alive
	 */
	public boolean isAlive() throws RemoteException;
	
	/**
	 * Kills/exits this worker
	 * @throws RemoteException
	 */
	public void exit() throws RemoteException;
	
	/**
	 * @return The {@link URI} address of this worker
	 * @throws RemoteException
	 */
	public URI getURI() throws RemoteException;

	/**
	 * @return The ratio of cache hits to cache misses
	 */
	public double getCacheRateRatio() throws RemoteException;
}
