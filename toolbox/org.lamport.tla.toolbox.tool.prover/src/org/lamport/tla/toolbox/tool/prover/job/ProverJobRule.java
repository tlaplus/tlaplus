package org.lamport.tla.toolbox.tool.prover.job;

import org.eclipse.core.runtime.jobs.ISchedulingRule;

/**
 * This is the scheduling rule that should be used
 * to run a ProverJob. It allows at most one prover
 * job to be running at any given time from the toolbox.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProverJobRule implements ISchedulingRule
{

    public boolean contains(ISchedulingRule rule)
    {
        return rule == this;
    }

    /**
     * Any job with an instance of this rule cannot
     * be run at the same time.
     */
    public boolean isConflicting(ISchedulingRule rule)
    {
        return rule instanceof ProverJobRule;
    }

}
