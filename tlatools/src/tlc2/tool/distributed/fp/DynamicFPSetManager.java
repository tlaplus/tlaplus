// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.fp;

import java.io.Serializable;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;

import tlc2.tool.distributed.TLCWorker;

/**
 * Contrary to {@link FPSetManager}, this class is a {@link UnicastRemoteObject}
 * . This results in it being a singleton for a distributed TLC model checker
 * and thus a single point of failure and bottleneck.<br>
 * On the up side, it results in {@link TLCWorker}s seeing a consistent
 * distributed fingerprint set at all times.
 */
@SuppressWarnings("serial")
public class DynamicFPSetManager extends FPSetManager implements Serializable {

	public DynamicFPSetManager(int expectedNumOfServers) throws RemoteException {
		super();
		// zero upper 32 bit
		//TODO calc mask based on expectedNumOfServers
		this.mask = 0x00000000FFFFFFFFL;
	}


	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#register(tlc2.tool.distributed.FPSetRMI)
	 */
	public synchronized int register(FPSetRMI aFPSet, String hostname) {
		fpSets.add(new FPSets(aFPSet, hostname));
		// not used right now
		return 0;
	}
}
