// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.distributed.consumer;

import java.net.URI;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import tlc2.IDistributedFPSet;

public class DistributedFPSetConsumer {
	
	/**
	 * TLCServer address to connect to.
	 * 
	 * //TODO refactor to read/obtain URI from ECF discovery
	 * //TODO port number currently hard coded in TLCServer/TLCWorker 
	 */
	private final URI uri = URI
			.create(System.getProperty(DistributedFPSetConsumer.class.getName()
					+ ".uri", "rmi://localhost:10997"));

	/**
	 * Instructs this instance that the {@link IDistributedFPSet} service is
	 * available in the OSGi lifecycle model.
	 * 
	 * @param anIDistributedFPSet
	 *            An {@link IDistributedFPSet} passed by OSGi Declarative
	 *            Services
	 */
	public void setIDistributedFPSet(final IDistributedFPSet anIDistributedFPSet) {
		// Fork out to a separate thread to not block DeclarativeService forever
		final ExecutorService executor = Executors.newSingleThreadExecutor();
		executor.execute(new Runnable() {
			/* (non-Javadoc)
			 * @see java.lang.Runnable#run()
			 */
			public void run() {
				anIDistributedFPSet.connect(uri);
			}
		});
	}

	/**
	 * Instructs this instance that the {@link IDistributedFPSet} service is
	 * gone in the OSGi lifecycle model.
	 * 
	 * @param anIDistributedFPSet
	 *            An {@link IDistributedFPSet} passed by OSGi Declarative
	 *            Services
	 */
	public void unsetIDistributedFPSet(final IDistributedFPSet anIDistributedFPSet) {
		anIDistributedFPSet.disconnect();
	}
}
