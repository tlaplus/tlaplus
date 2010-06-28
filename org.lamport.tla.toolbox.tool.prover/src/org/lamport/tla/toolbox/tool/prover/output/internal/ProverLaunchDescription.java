package org.lamport.tla.toolbox.tool.prover.output.internal;

import org.lamport.tla.toolbox.tool.prover.job.ProverJob;

import tla2sany.semantic.LevelNode;

/**
 * This class describes the parameters for the launch of a prover.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProverLaunchDescription
{

    /**
     * True iff the prover was
     * launched only for status checking.
     */
    private boolean statusCheck;
    /**
     * True iff proofs were checked.
     * Should not be true if status check
     * is also true.
     */
    private boolean checkProofs;
    /**
     * True iff fingerprints were
     * used.
     */
    private boolean useFP;
    /**
     * The step or module node on which the
     * prover was launched.
     */
    private LevelNode levelNode;
    /**
     * The instance of the job used to launch the prover.
     */
    private ProverJob proverJob;

    public ProverLaunchDescription(ProverJob proverJob, boolean useFP, boolean statusCheck, boolean checkProofs,
            LevelNode nodeToProve)
    {
        this.proverJob = proverJob;
        this.useFP = useFP;
        this.statusCheck = statusCheck;
        this.checkProofs = checkProofs;
        this.levelNode = nodeToProve;
    }

    public boolean isStatusCheck()
    {
        return statusCheck;
    }

    public boolean isCheckProofs()
    {
        return checkProofs;
    }

    public boolean isUseFP()
    {
        return useFP;
    }

    /**
     * Gets the step or module node on which the
     * prover was launched.
     * @return the levelNode
     */
    public LevelNode getLevelNode()
    {
        return levelNode;
    }

    /**
     * Returns the instance of the job used to launch the prover.
     * @return the proverJob
     */
    public ProverJob getProverJob()
    {
        return proverJob;
    }

}
