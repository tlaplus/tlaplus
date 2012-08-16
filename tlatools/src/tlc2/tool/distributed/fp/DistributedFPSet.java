// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.fp;

import java.io.File;
import java.net.InetAddress;
import java.net.MalformedURLException;
import java.rmi.ConnectException;
import java.rmi.Naming;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.distributed.TLCServer;
import tlc2.tool.distributed.TLCServerRMI;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MultiFPSet;
import util.TLCRuntime;
import util.ToolIO;

public class DistributedFPSet  {

	public static void main(String[] args) {
        System.out.println("TLC Distributed FP Server " + TLCGlobals.versionOfTLC);

        // Must have exactly one arg: a hostname (spec is read from the server
		// connecting to).
		if(args.length != 1) {
			printErrorMsg("Error: Missing hostname of the TLC server to be contacted.");
			return;
		}
		final String serverName = args[0];

		 //TODO read parameter fpbits?
		final int prefixBits = 0;

		try {
			// Lookup FPSetManager
			TLCServerRMI tlcServer = lookupTLCServer(serverName);
			
			// Create metadata directory
			final String metadir = System.getProperty("java.io.tmpdir") + File.separator + "FPSet"
					+ System.currentTimeMillis();
			final File filedir = new File(metadir);
			if (!filedir.exists()) {
				filedir.mkdirs();
			}
			
			// Initialize this FPSet with n-prefix bits and m mask bits
			final long fpMemSize = TLCRuntime.getInstance().getFPMemSize(1.);
			final FPSet fpSet = FPSet.getFPSet(prefixBits , fpMemSize / 8);
			final String filename = "FPSet" + System.currentTimeMillis();
			fpSet.init(0,metadir,filename);
			
			// Print out fpset type and nested FPSets when MultiFPSet
			System.err.println("FPSet instance type is: " + fpSet.getClass().getName());
			if (fpSet instanceof MultiFPSet) {
				final MultiFPSet multiFPSet = (MultiFPSet) fpSet;
				final FPSet[] fpSets = multiFPSet.getNestedFPSets();
				for (int i = 0; i < fpSets.length; i++) {
					System.err.println("...with nested instance type: " + fpSets[i].getClass().getName());
				}		
			}

			// Register this with the FPSetManager
			final String hostname = InetAddress.getLocalHost().getHostName();
			tlcServer.registerFPSet(fpSet, hostname);

			// Show FPset is ready accepting fingerprints
            System.out.println("Fingerprint set server at " + hostname + " is ready.");
			
			// Periodically report status (every 5 minutes)
			synchronized (fpSet) {
				while (true) {
					System.out.println("Progress: The number of fingerprints stored at " + hostname + " is "
							+ fpSet.size() + ".");
					fpSet.wait(300000);
				}
			}
		} catch (Throwable e) {
			// Assert.printStack(e);
			MP.printError(EC.GENERAL, e);
			ToolIO.out.println("Error: Failed to start worker "
					+ " for server " + serverName + ".\n" + e.getMessage());
		}
	
		ToolIO.out.flush();
	}
	
	private static TLCServerRMI lookupTLCServer(final String serverName) throws MalformedURLException, RemoteException, NotBoundException, InterruptedException {
		String url = "//" + serverName + ":" + TLCServer.Port
				+ "/TLCServer";

		// try to repeatedly connect to the server until it becomes available
		int i = 1;
		while(true) {
			try {
				return (TLCServerRMI) Naming.lookup(url);
			} catch (ConnectException e) {
				// if the cause if a java.NET.ConnectException the server is
				// simply not ready yet
				final Throwable cause = e.getCause();
				if(cause instanceof java.net.ConnectException) {
					long sleep = (long) Math.sqrt(i);
					ToolIO.out.println("Server " + serverName
							+ " unreachable, sleeping " + sleep
							+ "s for server to come online...");
					Thread.sleep(sleep * 1000);
					i *= 2;
				} else {
					// some other exception occurred which we do not know
					// how to handle
					throw e;
				}
			}
		}
	}
	
	private static void printErrorMsg(String msg) {
		ToolIO.out.println(msg);
		ToolIO.out
				.println("Usage: java " + DistributedFPSet.class.getName() + " host");
	}
}
