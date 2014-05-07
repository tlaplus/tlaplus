package org.lamport.tla.toolbox.jcloud;

import java.io.File;
import java.util.Properties;

import org.eclipse.core.runtime.jobs.Job;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJobFactory;

public class CloudTLCJobFactory implements TLCJobFactory {

	@Override
	public Job getTLCJob(String aName, File aModelFolder, int numberOfWorkers, final Properties props) {
		return new CloudDistributedTLCJob(aName, aModelFolder, numberOfWorkers, props);
	}

}
