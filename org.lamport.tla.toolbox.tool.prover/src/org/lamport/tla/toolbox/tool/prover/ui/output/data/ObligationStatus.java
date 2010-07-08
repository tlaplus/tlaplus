package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

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
     * Marker containing attributes about the
     * obligation. The attributes
     * 
     * {@link ProverHelper#OBLIGATION_ID}
     * {@link ProverHelper#OBLIGATION_STATE}
     * 
     * should always be present. However, for
     * dummy missing and omitted obligations,
     * the id is meaningless. The attribute
     * 
     * {@link ProverHelper#OBLIGATION_STRING}
     * 
     * may or may not be set depending on whether the
     * prover has sent the pretty printed form
     * of the obligation.
     */
    private IMarker obMarker;

    /**
     * Create an obligation with the parent step
     * and the marker for the obligation.
     * Calls {@link #setState(long)} on the initialState
     * 
     * @param parent the parent step of the obligation.
     * @param obMarker the marker for this obligation
     * which should already have the attributes
     * {@link ProverHelper#OBLIGATION_ID} and
     * {@link ProverHelper#OBLIGATION_STATE} set.
     * The attribute {@link ProverHelper#OBLIGATION_STRING}
     * need not be set yet.
     */
    public ObligationStatus(StepTuple parent, IMarker obMarker)
    {
        this.parent = parent;
        this.obMarker = obMarker;
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
        return obMarker.getAttribute(ProverHelper.OBLIGATION_STATE, -1);
    }

    // /**
    // * This method sets the current state of the
    // * obligation.
    // *
    // * If the value of the state has changed, this method
    // * calls {@link StepTuple#updateStatus()} on the parent
    // * of this obligation.
    // *
    // * @param newState
    // */
    // public void setState(int newState)
    // {
    // if (newState != obState)
    // {
    // obState = newState;
    // parent.updateStatus();
    // }
    // }

    /**
     * Updates the obligation with information
     * from the message. In particular, this updates
     * the state of the obligation and set the pretty
     * printed form of the obligation if that information
     * is in the message.
     * 
     * If the state of this obligation changes because of the message,
     * this method updates the status of the parent.
     * 
     * @param message
     */
    public void updateObligation(ObligationStatusMessage message)
    {

        try
        {
            /*
             * The obligation string is not sent by the prover for every message.
             * It is only sent once when the obligation is first interesting.
             * Thus, message.getObString() can be null. Everytime a new message comes
             * in for a given id, we set the obligation string. This way, when the obligation
             * string is actually sent by the prover, it is set on the marker.
             */
            obMarker.setAttribute(ProverHelper.OBLIGATION_STRING, message.getObString());

            // the old state of the obligation
            int oldState = obMarker.getAttribute(ProverHelper.OBLIGATION_STATE, -1);
            // the new state of the obligation
            int newState = ProverHelper.getIntFromStringStatus(message.getStatus(), oldState, message.getMethod());
            if (oldState != newState)
            {
                obMarker.setAttribute(ProverHelper.OBLIGATION_STATE, newState);
                parent.updateStatus();
            }
        } catch (CoreException e)
        {
            ProverUIActivator.logError("Error setting attributes for an obligation marker.", e);
        }

    }

    /**
     * Returns the {@link IMarker} containing attributes about the
     * obligation. The attributes
     * 
     * {@link ProverHelper#OBLIGATION_ID}
     * {@link ProverHelper#OBLIGATION_STATE}
     * 
     * should always be present. However, for
     * dummy missing and omitted obligations,
     * the id is meaningless. The attribute
     * 
     * {@link ProverHelper#OBLIGATION_STRING}
     * 
     * may or may not be set depending on whether the
     * prover has sent the pretty printed form
     * of the obligation.
     * @return
     */
    public IMarker getObMarker()
    {
        return obMarker;
    }
}
