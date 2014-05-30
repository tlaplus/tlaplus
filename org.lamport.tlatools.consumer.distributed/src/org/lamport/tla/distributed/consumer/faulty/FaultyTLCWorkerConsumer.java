// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.distributed.consumer.faulty;

import java.net.URI;

import tlc2.ITLCWorker;

/**
 * @author Markus Alexander Kuppe
 * 
 * <p> If DS does not pass an ITLCWorker, make sure that: 
 *  <ul>
 *   <li>The DS framework (org.eclipse.equinox.ds) is installed in active</li>
 *   <li>org.lamport.tlatools.impl.distributed is installed and active</li>
 *  </ul>
 * </p>
 */
public class FaultyTLCWorkerConsumer extends FaultyConsumer {

	/**
	 * TLCServer address to connect to.
	 * 
	 * //TODO refactor to read/obtain URI from ECF discovery
	 * //TODO port number currently hard coded in TLCServer/TLCWorker 
	 */
	private final URI uri = URI
			.create(System.getProperty(FaultyTLCWorkerConsumer.class.getName()
					+ ".uri", "rmi://localhost:10997"));

	/**
	 * @see OSGi-INF/component.xml
	 * @param anITLCWorker
	 *            passed by OSGi Declarative Services
	 */
	public void setITLCWorker(final ITLCWorker anITLCWorker) {
		// Fork out to a separate thread to not block the DeclarativeService forever
		executor.execute(new Runnable() {

			/* (non-Javadoc)
			 * @see java.lang.Runnable#run()
			 */
			public void run() {

				while(true) {

					// connect and wait for some states to be calculated (for three minutes max)
					anITLCWorker.connect(uri);
					long seconds = sleep();
					
					// disconnect from server and sleep before reconnecting again 
					System.err.println("Forcefully disconnecting TLCWorkers from TLCServer after " + seconds + "s" + "\n\n");
					anITLCWorker.disconnect();
					sleep();
				}
			}
		});
	}

	/**
	 * @see OSGi-INF/component.xml
	 * @param anITLCWorker passed by OSGi Declarative Services
	 */
	public void unsetITLCWorker(final ITLCWorker anITLCWorker) {
		anITLCWorker.disconnect();
	}
}
