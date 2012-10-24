// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
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

	private int expectedNumOfServers;

	public DynamicFPSetManager(int expectedNumOfServers) throws RemoteException {
		super();
		this.expectedNumOfServers = expectedNumOfServers;
		
		// Guard against invalid values
		if (expectedNumOfServers <= 0) {
			throw new IllegalArgumentException();
		}
		
		// Round expectedNumOfServers to power of 2
		int log = 0;
		while (expectedNumOfServers > 0) {
			expectedNumOfServers = expectedNumOfServers / 2;
			log++;
		}
		
		// Zero upper bits of mask which won't be used when addressing the
		// fingerprint servers anyway.
		this.mask = (1L << log) - 1L;
	}


	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#register(tlc2.tool.distributed.FPSetRMI)
	 */
	public synchronized void register(FPSetRMI aFPSet, String hostname) throws FPSetManagerException {
		// Only accept additional FPSets as long as we haven't reached the
		// expected number of FPSets. Adding more FPSets to the set than
		// expected, would screw up the fail over code in reassign() as workers
		// potentially see an inconsistent list of FPSets.
		// This is due to the fact that workers immediately retrieve the
		// FPSetManager once the expected number of FPSets have registered.
		if (fpSets.size() < expectedNumOfServers) {
		        fpSets.add(new FPSets(aFPSet, hostname));
		} else {
		        throw new FPSetManagerException(
		                        "Limit for FPset servers reached (" + expectedNumOfServers
		                                        + "). Cannot handle additional servers");
		}
	}
}
