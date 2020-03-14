// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.distributed.consumer;

import java.net.URI;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import org.osgi.framework.Bundle;
import org.osgi.framework.BundleContext;
import org.osgi.framework.FrameworkUtil;
import org.osgi.service.packageadmin.PackageAdmin;

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
@SuppressWarnings("deprecation")
public class TLCWorkerConsumer {

	/**
	 * TLCServer address to connect to.
	 * 
	 * //TODO refactor to read/obtain URI from ECF discovery
	 * //TODO port number currently hard coded in TLCServer/TLCWorker 
	 */
	private final URI uri = URI
			.create(System.getProperty(TLCWorkerConsumer.class.getName()
					+ ".uri", "rmi://localhost:10997"));
	
	private PackageAdmin pa;

	public void setPackageAdmin(PackageAdmin pa) {
		this.pa = pa;
	}
	
	/**
	 * @see OSGi-INF/component.xml
	 * @param anITLCWorker
	 *            passed by OSGi Declarative Services
	 */
	public void setITLCWorker(final ITLCWorker anITLCWorker) {
		final ExecutorService executor = Executors.newSingleThreadExecutor();
		executor.submit(new Callable<Void>() {

			public Void call() throws Exception {
				try {
					// a) Connect and wait for some states to be calculated
					System.out.println(String.format("Connecting new TLCWorker %s to url %s", anITLCWorker, uri));
					anITLCWorker.connect(uri);
					
					// b) Wait for this model checker run to be done
					anITLCWorker.awaitTermination();
				} finally {
					// c) Refresh the OSGi bundle
					System.out.println("Disposing old tlatools bundle...");
					BundleContext bundleContext = FrameworkUtil.getBundle(
							TLCWorkerConsumer.class).getBundleContext();

					final Bundle bundle = getTlaToolsBundle();
					final String location = bundle.getLocation();
					bundle.stop();
					bundle.uninstall();
					Bundle newBundleInstance = bundleContext
							.installBundle(location);
					newBundleInstance.start();
					pa.refreshPackages(new Bundle[] { bundle });
				}
				return null;
			}
		});
	}
	
	private Bundle getTlaToolsBundle() {
		BundleContext ctx = FrameworkUtil.getBundle(
				TLCWorkerConsumer.class).getBundleContext();
		final Bundle[] bundles = ctx.getBundles();
		for (Bundle bundle : bundles) {
			if ("org.lamport.tlatools".equals(bundle.getSymbolicName())) {
				return bundle;
			}
		}
		// Getting here is very bad and means my assumptions about the
		// environment are incorrect, sorry :-(
		return null;
	}

	/**
	 * @see OSGi-INF/component.xml
	 * @param anITLCWorker passed by OSGi Declarative Services
	 */
	public void unsetITLCWorker(final ITLCWorker anITLCWorker) {
		anITLCWorker.disconnect();
	}
}
