package org.lamport.tla.toolbox.tool.prover.ui.output.data;

/**
 * A class that represents the current status of an obligation.
 * 
 * @author Daniel Ricketts
 *
 */
public class ObligationStatus implements IStatusProvider
{

    private StepTuple parent;
    private int status;

    /**
     * Create an obligation with the parent step
     * and the initial status of the obligation.
     * 
     * @param parent
     * @param initialStatus
     */
    public ObligationStatus(StepTuple parent, int initialStatus)
    {
        this.parent = parent;
        this.status = initialStatus;
    }

    /**
     * Returns the current status of the obligation.
     */
    public int getStatus()
    {
        return status;
    }

    /**
     * Sets the status and tells the parent step to
     * update its status.
     * 
     * @param status
     */
    public void setStatus(int status)
    {
        this.status = status;
        parent.updateStatus();
    }

}
