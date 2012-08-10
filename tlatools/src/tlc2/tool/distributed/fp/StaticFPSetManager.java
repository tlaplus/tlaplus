// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.fp;

import java.net.MalformedURLException;
import java.rmi.Naming;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.util.ArrayList;
import java.util.List;

@SuppressWarnings("serial")
public class StaticFPSetManager extends FPSetManager {

	public StaticFPSetManager(FPSetRMI fpSet) {
		super(fpSet);
	}

	/**
	 * Constructed from a list of hostnames of fpset servers. We require that
	 * all the fp servers be available initially.
	 */
	public StaticFPSetManager(String[] hosts) throws RemoteException,
			NotBoundException, MalformedURLException {
		super(convert(hosts));
	}
	
	private static List<FPSets> convert(String[] hosts) throws MalformedURLException, RemoteException, NotBoundException {
		List<FPSets> res = new ArrayList<FPSets>(hosts.length);
		for (int i = 0; i < hosts.length; i++) {
			String url = "//" + hosts[i] + ":" + Port + "/FPSetServer";
			FPSetRMI fpset = (FPSetRMI) Naming.lookup(url);
			res.add(new FPSets(fpset, hosts[i]));
		}
		return res;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#register(tlc2.tool.distributed.fp.FPSetRMI, java.lang.String)
	 */
	public int register(FPSetRMI fpset, String hostname) {
		throw new UnsupportedOperationException("Not applicable for static FPSetManager");
	}
}
