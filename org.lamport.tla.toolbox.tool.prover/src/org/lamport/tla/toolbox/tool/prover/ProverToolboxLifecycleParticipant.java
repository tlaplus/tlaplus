package org.lamport.tla.toolbox.tool.prover;

import org.lamport.tla.toolbox.lifecycle.ToolboxLifecycleParticipant;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

/**
 * This class gets notified when the toolbox starts up and shuts down.
 * When it shuts down, it cancels all running prover jobs.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProverToolboxLifecycleParticipant extends ToolboxLifecycleParticipant
{

    public ProverToolboxLifecycleParticipant()
    {
        // TODO Auto-generated constructor stub
    }

    /**
     * Is called during termination of the toolbox. 
     * This implementation cancels all running prover jobs.
     */
    public void terminate()
    {

        ProverHelper.cancelProverJobs(true);

    }

}
