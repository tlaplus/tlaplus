package org.lamport.tla.toolbox.tool.tlc;

import org.eclipse.core.runtime.jobs.Job;
import org.lamport.tla.toolbox.tool.ToolboxLifecycleException;
import org.lamport.tla.toolbox.tool.ToolboxLifecycleParticipant;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJob;

/**
 * Stop all running org.lamport.tla.toolbox.tool.tlc jobs on shutdown
 * 
 * @author Simon Zambrovski
 */
public class TLCLifecycleParticipant extends ToolboxLifecycleParticipant {

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.ToolboxLifecycleParticipant#terminate()
	 */
	public void terminate() throws ToolboxLifecycleException {
		Job.getJobManager().cancel(TLCJob.AllJobsMatcher);
	}
}
