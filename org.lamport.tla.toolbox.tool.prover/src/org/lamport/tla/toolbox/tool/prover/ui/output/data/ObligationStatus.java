package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

import tla2sany.st.Location;

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
     * A map from the name of backends
     * to the String representing the most
     * recent status of the backend on this obligation.
     */
    private Map proverStatuses;

    /**
     * Create an obligation with the parent step
     * and the marker for the obligation. The parent step
     * can be null if the parent is to be set later using
     * {@link #setParent(StepTuple)}.
     * Calls {@link #setState(long)} on the initialState
     * 
     * @param parent the parent step of the obligation. Can be null
     * if the parent is to be set later using {@link #setParent(StepTuple)}.
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
        this.proverStatuses = new HashMap();
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

    /**
     * Returns a map from the name of backends
     * to the String representing the most
     * recent status of the backend on this obligation.
     * @return
     */
    public Map getProverStatuses()
    {
        return proverStatuses;
    }

    /**
     * Returns the parent {@link StepTuple} of this
     * obligation. Will be null if it has not yet been
     * set using {@link #setParent(StepTuple)}.
     * @return
     */
    public StepTuple getParent()
    {
        return parent;
    }

    /**
     * Sets the parent step of this obligation.
     * @param parentStep
     */
    public void setParent(StepTuple parentStep)
    {
        this.parent = parentStep;
    }

    /**
     * Returns the id of the obligation.
     * @return
     */
    public int getId()
    {
        return obMarker.getAttribute(ProverHelper.OBLIGATION_ID, -1);
    }

    public String getObligationString()
    {
        return getObMarker().getAttribute(ProverHelper.OBLIGATION_STRING, "");
    }

    /**
     * Returns a string description of the most
     * recent status of each prover on each backend.
     * 
     * @return
     */
    public String getProverStatusString()
    {
        StringBuilder buffer = new StringBuilder();
        Set entrySet = proverStatuses.entrySet();
        for (Iterator it = entrySet.iterator(); it.hasNext();)
        {
            Map.Entry nextEntry = (Map.Entry) it.next();
            // the key is the name of the backend, the value is the status
            // on that backend
            buffer.append(nextEntry.getKey() + " : " + nextEntry.getValue());
            if (it.hasNext())
            {
                buffer.append(" , ");
            }
        }

        return buffer.toString();
    }

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

            /*
             * Update the most recent status of the given backend.
             */
            if (message.getBackend() != null && message.getStatus() != null)
            {
                proverStatuses.put(message.getBackend(), message.getStatus());
            }

            int oldState = getObligationState();
            // the new state of the obligation
            int newState = ProverHelper.getIntFromStringStatus(message.getStatus(), oldState, message.getBackend());
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

    /**
     * Returns the location of the obligation that was reported by tlapm.
     * Note that this is not necessarily the current locaion of the marker
     * representing this obligation.
     * 
     * @return
     */
    public Location getTLAPMLocation()
    {
        return ProverHelper.stringToLoc(obMarker.getAttribute(ProverHelper.OBLIGATION_LOCATION, ""));
    }
}
