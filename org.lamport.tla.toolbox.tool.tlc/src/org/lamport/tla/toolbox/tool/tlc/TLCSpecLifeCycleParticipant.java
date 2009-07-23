package org.lamport.tla.toolbox.tool.tlc;

import org.eclipse.core.runtime.jobs.Job;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;

/**
 * React on spec operations with cancellation of the corresponding processes  
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCSpecLifeCycleParticipant extends SpecLifecycleParticipant
{

    public TLCSpecLifeCycleParticipant()
    {

    }

    public boolean eventOccured(SpecEvent event)
    {
        // System.out.println(event.toString());
        switch (event.getType()) {
        case SpecEvent.TYPE_CLOSE:
        case SpecEvent.TYPE_DELETE:
        case SpecEvent.TYPE_RENAME:

            Job[] runningSpecJobs = Job.getJobManager().find(event.getSpec());
            for (int i = 0; i < runningSpecJobs.length; i++)
            {
                // send cancellations to all jobs...
                runningSpecJobs[i].cancel();
            }
            break;
        default:
            break;
        }
        return true;
    }
}
