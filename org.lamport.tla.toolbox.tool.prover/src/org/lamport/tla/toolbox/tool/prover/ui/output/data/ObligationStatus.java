package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IMarker;
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
     * 
     * should always be present. However, for
     * dummy missing and omitted obligations,
     * the id is meaningless.
     */
    private IMarker obMarker;
    /**
     * A map from the name of backends
     * to the String representing the most
     * recent status of the backend on this obligation.
     */
    private Map proverStatuses;
    /**
     * The pretty printed form of the obligation. This
     * can be null if the obligation string has not been sent.
     */
    private String obligationString;
    /**
     * The current obligation state. See
     * {@link ColorPredicate} for an explanation
     * of obligation states.
     */
    private int obState;
    /**
     * The id of the obligation given by tlapm.
     */
    private int id;
    /**
     * The location of the obligation that was reported by tlapm.
     * Note that this is not necessarily the current location of the marker
     * representing this obligation.
     */
    private Location location;

    /**
     * Create an obligation with the parent step,
     * the marker for the obligation, and initial state. The parent step
     * can be null if the parent is to be set later using
     * {@link #setParent(StepTuple)}.
     * Calls {@link #setState(long)} on the initialState
     * 
     * @param parent the parent step of the obligation. Can be null
     * if the parent is to be set later using {@link #setParent(StepTuple)}.
     * @param obMarker the marker for this obligation
     * which should already have the attributes
     * {@link ProverHelper#OBLIGATION_ID} set.
     * @param initialState the initial state of the obligation. See
     * {@link ColorPredicate} for an explanation of obligation states.
     * @param location the location of the obligation as reported by tlapm
     * @param id the id of the obligation as given by tlapm
     */
    public ObligationStatus(StepTuple parent, IMarker obMarker, int initialState, Location location, int id)
    {
        this.parent = parent;
        this.proverStatuses = new HashMap();
        this.obState = initialState;
        this.id = id;
        this.location = location;
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
        return id;
    }

    /**
     * Returns the pretty printed form of the obligation. This
     * can be null if the obligation string has not been sent.
     */
    public String getObligationString()
    {
        return obligationString;
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
        /*
         * The obligation string is not sent by the prover for every message.
         * It is only sent once when the obligation is first interesting.
         * Thus, message.getObString() can be null. Everytime a new message comes
         * in for a given id, we set the obligation string.
         */
        this.obligationString = message.getObString();
        // obMarker.setAttribute(ProverHelper.OBLIGATION_STRING, message.getObString());

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
            // obMarker.setAttribute(ProverHelper.OBLIGATION_STATE, newState);
            obState = newState;

            parent.updateStatus();
        }

    }

    /**
     * Returns the {@link IMarker} containing attributes about the
     * obligation. The attributes
     * 
     * {@link ProverHelper#OBLIGATION_ID}
     * 
     * should always be present. However, for
     * dummy missing and omitted obligations,
     * the id is meaningless.
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
        return location;
    }
}
