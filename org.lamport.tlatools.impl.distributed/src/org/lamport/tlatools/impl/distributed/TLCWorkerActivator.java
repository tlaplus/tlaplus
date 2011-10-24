// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package org.lamport.tlatools.impl.distributed;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;

import org.eclipse.core.runtime.FileLocator;
import org.osgi.framework.Bundle;
import org.osgi.framework.BundleActivator;
import org.osgi.framework.BundleContext;

public class TLCWorkerActivator implements BundleActivator {

	private static BundleContext context;

	static BundleContext getContext() {
		return context;
	}

	/*
	 * (non-Javadoc)
	 * @see org.osgi.framework.BundleActivator#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext bundleContext) throws Exception {
		TLCWorkerActivator.context = bundleContext;
	}

	/*
	 * (non-Javadoc)
	 * @see org.osgi.framework.BundleActivator#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext bundleContext) throws Exception {
		TLCWorkerActivator.context = null;
	}

	/**
	 * Find the tla bundle within the list of all installed bundles
	 * @param aSymbolicName 
	 */
	private static Bundle getTLABundle(final String aSymbolicName) throws IOException {
		final Bundle[] bundles = context.getBundles();
		for (final Bundle bundle : bundles) {
			final String symbolicName = bundle.getSymbolicName();
			if(aSymbolicName.equals(symbolicName)) {
				return bundle;
			}
		}
		throw new IOException("Cannot find TLA bundle");
	}

	public static String[] getEntries(final String symbolicName, final String path, final String pattern) throws IOException {
		// try to find the tla bundle that contains STANDARD_MODULES/ folder
		final Bundle bundle = getTLABundle(symbolicName);

		// The TLA bundle contains the standard modules in the standard_modules_folder
		final Enumeration<URL> entries = bundle.findEntries(path, pattern, true);
		
		// convert the OSGi specific path to a generic path that can be
		// understood by the superclass
		final List<String> paths = new ArrayList<String>();
		while (entries.hasMoreElements()) {
			final URL library = entries.nextElement();
			if (library != null) {
				// add external (resolved) URL
				paths.add(FileLocator.resolve(library).getPath());
			}
		}
		return paths.toArray(new String[paths.size()]);
	}
}
