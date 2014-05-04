package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.File;

import org.eclipse.core.runtime.jobs.Job;

public interface TLCJobFactory {

	Job getTLCJob(String aName, File aModelFolder, int numberOfWorkers);
}
