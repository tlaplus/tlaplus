package org.lamport.tla.toolbox.jcloud;

import org.osgi.framework.BundleActivator;
import org.osgi.framework.BundleContext;

public class JCloudActivator implements BundleActivator {

	@Override
	public void start(BundleContext ctx) throws Exception {
//		final Properties props = new Properties();
//		props.put("cloud", "aws-ec2");
//		ctx.registerService(TLCJob.class, new ServiceFactory<TLCJob>() {
//
//			@Override
//			public TLCJob getService(Bundle bundle,
//					ServiceRegistration<TLCJob> registration) {
//				return new CloudDistributedTLCJob("");
//			}
//
//			@Override
//			public void ungetService(Bundle bundle,
//					ServiceRegistration<TLCJob> registration, TLCJob service) {
//			}
//		}, props);
//		
//        File path = new File("/home/markus/src/TLA/models/Grid5kPerformanceTest/Test.toolbox/k8l8n6");
//		Job j = new CloudDistributedTLCJob("foo", path, 1);
//		j.schedule();
	}

	@Override
	public void stop(BundleContext ctx) throws Exception {
		
	}
}
