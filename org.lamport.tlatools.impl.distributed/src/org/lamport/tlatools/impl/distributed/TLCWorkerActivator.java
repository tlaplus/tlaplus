// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package org.lamport.tlatools.impl.distributed;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;

import org.eclipse.osgi.service.urlconversion.URLConverter;
import org.osgi.framework.Bundle;
import org.osgi.framework.BundleActivator;
import org.osgi.framework.BundleContext;
import org.osgi.framework.Filter;
import org.osgi.framework.InvalidSyntaxException;
import org.osgi.util.tracker.ServiceTracker;

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
				// Get the OSGi URLConverter
				URLConverter urlConverter = getURLConverter(library);
				// add external (resolved) URL
				paths.add(urlConverter.resolve(library).getPath());
			}
		}
		return paths.toArray(new String[paths.size()]);
	}
	
	/*
	 * Return the URL Converter for the given URL. Return null if we can't
	 * find one.
	 */
	@SuppressWarnings({ "rawtypes", "unchecked" })
	private static URLConverter getURLConverter(URL url) {
		// get the right service based on the protocol
		String FILTER_PREFIX = "(&(objectClass=" + URLConverter.class.getName() + ")(protocol=";
		String FILTER_POSTFIX = "))";
		Filter filter = null;
		try {
			filter = getContext().createFilter(FILTER_PREFIX + url.getProtocol() + FILTER_POSTFIX);
		} catch (InvalidSyntaxException e) {
			// may not happen
			e.printStackTrace();
			return null;
		}
		
		ServiceTracker tracker = new ServiceTracker(getContext(), filter, null);
		tracker.open();
		return (URLConverter) tracker.getService();
	}
}
