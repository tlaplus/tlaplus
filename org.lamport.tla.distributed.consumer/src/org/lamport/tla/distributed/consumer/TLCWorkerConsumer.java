// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.distributed.consumer;

import java.net.URI;
import java.util.Random;
import java.util.concurrent.Executor;
import java.util.concurrent.Executors;

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
public class TLCWorkerConsumer {
	
	/**
	 * The upper bound for the sleep period between TLCServer connects and
	 * disconnects in seconds.
	 */
	private final int sleepUpperBound = Integer.getInteger(
			TLCWorkerConsumer.class.getName() + ".sleep", 180);

	/**
	 * TLCServer address to connect to.
	 * 
	 * //TODO refactor to read/obtain URI from ECF discovery
	 * //TODO port number currently hard coded in TLCServer/TLCWorker 
	 */
	private final URI uri = URI
			.create(System.getProperty(TLCWorkerConsumer.class.getName()
					+ ".uri", "rmi://localhost:10997"));

	/**
	 * @see OSGi-INF/component.xml
	 * @param anITLCWorker
	 *            passed by OSGi Declarative Services
	 */
	public void setITLCWorker(final ITLCWorker anITLCWorker) {
		final Executor executor = Executors.newSingleThreadExecutor();
		
		executor.execute(new Runnable() {

			private final Random rnd = new Random();

			/* (non-Javadoc)
			 * @see java.lang.Runnable#run()
			 */
			public void run() {

				while(true) {

					// connect and wait for some states to be calculated (for three minutes max)
					anITLCWorker.connect(uri);
					long seconds = sleep();
					
					// disconnect from server and sleep before reconnecting again 
					System.err.println("Forcefully disconnecting from TLCServer after " + seconds + "s" + "\n\n");
					anITLCWorker.disconnect();
					sleep();
				}
			}

			/**
			 * @param upperBound The upper bound for the thread to sleep
			 * @return The actual sleep time in seconds
			 */
			private long sleep() {
				long seconds = rnd.nextInt(sleepUpperBound);
				try {
					// add least 1 second
					Thread.sleep((seconds + 1) * 1000);
				} catch (InterruptedException e) {
					e.printStackTrace();
				}
				return seconds;
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
