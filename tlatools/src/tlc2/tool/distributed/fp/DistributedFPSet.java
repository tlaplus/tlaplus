// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
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
import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.FPSetFactory;
import tlc2.tool.fp.MultiFPSet;
import util.ToolIO;

public class DistributedFPSet  {

	private static volatile boolean running = true;

	public static void main(String[] args) {
		ToolIO.out.println("TLC Distributed FP Server " + TLCGlobals.versionOfTLC);

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
			final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration(1.0d);
			fpSetConfiguration.setFpBits(1 + prefixBits);
			final FPSet fpSet = FPSetFactory.getFPSet(fpSetConfiguration);
			final String filename = "FPSet" + System.currentTimeMillis();
			fpSet.init(1,metadir,filename);
			
			// Print out fpset type and nested FPSets when MultiFPSet
			System.err.println("FPSet instance type is: " + fpSet.getClass().getName());
			if (fpSet instanceof MultiFPSet) {
				final MultiFPSet multiFPSet = (MultiFPSet) fpSet;
				final FPSet[] fpSets = multiFPSet.getFPSets();
				for (int i = 0; i < fpSets.length; i++) {
					System.err.println("...with nested instance type: " + fpSets[i].getClass().getName());
				}
			}

			// Register this with the FPSetManager
			final String hostname = InetAddress.getLocalHost().getHostName();
			try {
				tlcServer.registerFPSet(fpSet, hostname);
			} catch (FPSetManagerException e) {
				// Registration as an FPSet has failed, un-export local FPSet and
				// exit main thread. Do not System.exit(int) as worker thread might 
				// run in this VM instance.
				fpSet.unexportObject(false);
				ToolIO.out.println(e.getMessage());
				return;
			}

			// Show FPset is ready accepting fingerprints
            System.out.println("Fingerprint set server at " + hostname + " is ready.");
			
			// Periodically report status (every 5 minutes)
			synchronized (fpSet) {
				while (running) {
					ToolIO.out.println("Progress: The number of fingerprints stored at " + hostname + " is "
							+ fpSet.size() + ".");
					fpSet.wait(300000);
				}
				
				// exit if signal received
				fpSet.unexportObject(false);
				ToolIO.out.println("Exiting TLC Distributed FP Server");
			}
		} catch (Throwable e) {
			// Assert.printStack(e);
			MP.printError(EC.GENERAL, e);
			ToolIO.out.println("Error: Failed to start FPSet "
					+ " for server " + serverName + ".\n" + e.getMessage());
		}
	
		ToolIO.out.flush();
	}

	/**
	 * Signal the {@link DistributedFPSet} to shutdown which results in a RMI
	 * de-registration by un-exporting the nested {@link FPSet}.
	 */
	public static void shutdown() {
		running = false;
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
