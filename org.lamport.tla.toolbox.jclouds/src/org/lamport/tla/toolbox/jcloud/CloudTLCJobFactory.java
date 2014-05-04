package org.lamport.tla.toolbox.jcloud;

import java.io.File;

import org.eclipse.core.runtime.jobs.Job;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJobFactory;

public class CloudTLCJobFactory implements TLCJobFactory {

	@Override
	public Job getTLCJob(String aName, File aModelFolder, int numberOfWorkers) {
		return new CloudDistributedTLCJob(aName, aModelFolder, numberOfWorkers);
	}

}
