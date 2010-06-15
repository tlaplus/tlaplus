package org.lamport.tla.toolbox.tool.prover.output.internal;

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
     * Start line sent to the prover. -1
     * if entire module was specified.
     */
    private int startLine;
    /**
     * The step or module node on which the
     * prover was launched.
     */
    private LevelNode levelNode;

    public boolean isStatusCheck()
    {
        return statusCheck;
    }

    public void setStatusCheck(boolean statusCheck)
    {
        this.statusCheck = statusCheck;
    }

    public boolean isCheckProofs()
    {
        return checkProofs;
    }

    public void setCheckProofs(boolean checkProofs)
    {
        this.checkProofs = checkProofs;
    }

    public boolean isUseFP()
    {
        return useFP;
    }

    public void setUseFP(boolean useFP)
    {
        this.useFP = useFP;
    }

    public int getStartLine()
    {
        return startLine;
    }

    public void setStartLine(int startLine)
    {
        this.startLine = startLine;
    }

    public int getEndLine()
    {
        return endLine;
    }

    public void setEndLine(int endLine)
    {
        this.endLine = endLine;
    }

    /**
     * Sets the step or module node on which the
     * prover was launched.
     * @param levelNode the levelNode to set
     */
    public void setLevelNode(LevelNode levelNode)
    {
        this.levelNode = levelNode;
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
     * End line sent to the prover. -1
     * if entire module was was specified.
     */
    private int endLine;

}
