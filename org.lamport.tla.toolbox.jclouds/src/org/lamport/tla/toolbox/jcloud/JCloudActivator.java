package org.lamport.tla.toolbox.jcloud;

import org.eclipse.core.runtime.jobs.Job;
import org.osgi.framework.BundleActivator;
import org.osgi.framework.BundleContext;

public class JCloudActivator implements BundleActivator {

	@Override
	public void start(BundleContext arg0) throws Exception {
		Job j = new CloudDistributedTLCJob("foo");
		j.schedule();
	}

	@Override
	public void stop(BundleContext arg0) throws Exception {
		
	}
}
