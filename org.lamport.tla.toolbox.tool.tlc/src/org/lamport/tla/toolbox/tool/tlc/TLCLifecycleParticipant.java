package org.lamport.tla.toolbox.tool.tlc;

import org.eclipse.core.runtime.jobs.Job;
import org.lamport.tla.toolbox.tool.ToolboxLifecycleException;
import org.lamport.tla.toolbox.tool.ToolboxLifecycleParticipant;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJob;

/**
 * Stop all running jobs on shutdown
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCLifecycleParticipant extends ToolboxLifecycleParticipant
{
    

    public TLCLifecycleParticipant()
    {
    }

    
    public void terminate() throws ToolboxLifecycleException
    {
        Job[] runningSpecJobs = Job.getJobManager().find(new TLCJob.AllJobMatcher());
        for (int i = 0; i < runningSpecJobs.length; i++)
        {
            // send cancellations to all jobs...
            runningSpecJobs[i].cancel();
        }
        // System.out.println("TLC: system is going down");
    }


    public void initialize() throws ToolboxLifecycleException
    {
        // System.out.println("TLC: system is going up");
    }

}
