package org.lamport.tla.toolbox.tool.prover.ui.output.data;

/**
 * A class that represents the current state of an obligation.
 * 
 * @author Daniel Ricketts
 *
 */
public class ObligationStatus
{

    /**
     * The parent step of this
     * obligation.
     */
    private StepTuple parent;
    /**
     * Int giving the number of the obligation state.
     * Check {@link ColorPredicate} for an explanation.
     */
    private int obState;

    /**
     * Create an obligation with the parent step
     * and the initial status of the obligation.
     * Calls {@link #setState(long)} on the initialState
     * 
     * @param parent the parent step of the obligation.
     * @param initialState the initial state of the obligation. See
     * {@link ColorPredicate} for an explanation of obligation states.
     */
    public ObligationStatus(StepTuple parent, int initialState)
    {
        this.parent = parent;
        setState(initialState);
    }

    /**
     * Returns the current obligation state. See
     * {@link ColorPredicate} for an explanation
     * of obligation states.
     * 
     * @return
     */
    public int getObligationState()
    {
        return obState;
    }

    /**
     * This method sets the current state of the
     * obligation.
     * 
     * If the value of the state has changed, this method
     * calls {@link StepTuple#updateStatus()} on the parent
     * of this obligation.
     * 
     * @param newState
     */
    public void setState(int newState)
    {
        if (newState != obState)
        {
            obState = newState;
            parent.updateStatus();
        }
    }

}
