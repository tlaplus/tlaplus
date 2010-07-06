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
    /**
     * Int giving the number of the obligation state.
     * Check {@link ColorPredicate} for an explanation.
     */
    private int obState;

    // /**
    // * The ith element of the array gives
    // * the value of the (i+1)st color predicate
    // * for this obligation. Color predicates
    // * are numbered starting at 1.
    // */
    // private boolean[] colorPredStatus;

    /**
     * Create an obligation with the parent step
     * and the initial status of the obligation.
     * Calls {@link #setStatus(long)}.
     * 
     * @param parent
     * @param initialStatus
     * @param proverJob the job used to launch the prover that led
     * to the creation of this obligation status
     */
    public ObligationStatus(StepTuple parent, int initialStatus)
    {
        this.parent = parent;
        // colorPredStatus = null;
        setStatus(initialStatus);
    }

    // /**
    // * Returns the current value of the color predicates for
    // * this obligation.
    // */
    // public boolean[] getColorPredicateValues()
    // {
    // return colorPredStatus;
    // }

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
     * obligation and recomputes the color predicates
     * for this obligation if the current state has changed.
     * 
     * If the value of any of the color predicates has changed,
     * this method calls {@link StepTuple#updateStatus()} on the
     * parent step.
     * 
     * @param newState
     */
    public void setStatus(int newState)
    {
        if (newState != obState)
        {
            obState = newState;
            // /*
            // * This method updates the parent
            // * if the color predicates have not been created at all
            // * or if at least one value has changed.
            // */
            // boolean updateParents = false;
            // if (colorPredStatus == null)
            // {
            // colorPredStatus = new boolean[ProverPreferencePage.NUM_STATUS_COLORS];
            // updateParents = true;
            // }
            //
            // // recompute the color predicates
            // ColorPredicate[] colorPredicates = proverJob.getColorPredicates();
            // for (int i = 0; i < ProverPreferencePage.NUM_STATUS_COLORS; i++)
            // {
            // boolean newPredStatus = colorPredicates[i].satisfiedByObligations(new int[] { this.obState });
            // colorPredStatus[i] = newPredStatus;
            // // update the parent if at least one color predicate value has changed.
            // updateParents = updateParents || (colorPredStatus[i] != newPredStatus);
            // }
            // if (updateParents)
            // {
            parent.updateStatus();
            // }
        }
    }

}
