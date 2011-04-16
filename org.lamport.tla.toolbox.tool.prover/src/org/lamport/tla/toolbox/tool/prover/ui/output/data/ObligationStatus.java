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
     * A map from the String name of backends
     * to the String representing the most
     * recent status of the backend on this obligation.
     * Constants representing possible obligation
     * statuses on backends appear in {@link ProverHelper}.
     */
    private Map proverStatuses;
    
    /**
     * A map from the String name of backends to the
     * most recent reason given for the backend.
     */
    private Map proverReasons;
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
     * {@link ProverHelper#OBLIGATION_ID} set. Can be null if this
     * is a dummy obligation because the marker is never used.
     * @param initialState the initial state of the obligation. See
     * {@link ColorPredicate} for an explanation of obligation states.
     * @param location the location of the obligation as reported by tlapm
     * @param id the id of the obligation as given by tlapm
     */
    public ObligationStatus(StepTuple parent, IMarker obMarker, int initialState, Location location, int id)
    {
        this.parent = parent;
        this.proverStatuses = new HashMap();
        this.proverReasons = new HashMap();
        this.obState = initialState;
        this.id = id;
        this.location = location;
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
     * Modified by LL on 16 April 2011 to add the reasons to the string.
     * This may have to be changed when the final exact form of the reason
     * field returned by tlapm is determined.
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
            String key = (String) nextEntry.getKey();
            String reason = (String) proverReasons.get(key);
            if (reason != null && !reason.equals("") && !reason.equals("false")) {
                reason = " (" + reason + ")";
            } else {
                reason = "";
            }
            buffer.append(key + " : " + nextEntry.getValue() + reason );
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
         * If the backend in the message already has a status of "proved" for this obligation,
         * then this message should be ignored. All subsequent messages should also be ignored.
         * This is done because there is no guarantee of the order in which obligation
         * status messages will be sent. For example, if the user
         * interrupts a backend in the middle of proving an obligation, then runs the prover again
         * and that same backend succeeds on the obligation, then the fingerprint file stores the information
         * that the obligation was interrupted on that backend and that it succeeded on that backend.
         * When a status check is done, the prover will send the message that the backend was interrupted
         * and that it succeeded, but there is no guarantee about the order in which that will happen.
         * Thus, we ignore all messages for a given backend for a given obligation once we receive the message
         * that that backend has proved that obligation.
         */
        String oldStatusOnBackend = (String) proverStatuses.get(message.getBackend());
        if (oldStatusOnBackend != null && oldStatusOnBackend.equals(ProverHelper.PROVED))
        {
            return;
        }

        /*
         * The obligation string is not sent by the prover for every message.
         * It is only sent once when the obligation is first interesting.
         * Thus, message.getObString() can be null. If the obligation string
         * has not yet been sent, we set it to the value of the obligation string
         * in the message. After the first time the obligation string has been set,
         * we do not set it again. Subsequent messages may not contain the obligation string
         * after the first one that does.
         */
        if (this.obligationString == null || this.obligationString.isEmpty())
        {
            this.obligationString = message.getObString();
        }

        /*
         * Update the most recent status of the given backend.
         */
        if (message.getBackend() != null && message.getStatus() != null)
        {
            proverStatuses.put(message.getBackend(), message.getStatus());
        }
        
        /*
         * The following code added by LL on 16 April 2011.
         * Update the most recent reason of the given backend.
         */
        if (message.getBackend() != null && message.getReason() != null)
        {
            proverReasons.put(message.getBackend(), message.getReason());
        }

        int oldState = getObligationState();
        // the new state of the obligation
        int newState = ProverHelper.getIntFromStringStatus(message.getStatus(), oldState, message.getBackend());
        if (oldState != newState)
        {
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
     * should always be present. This marker
     * will be null for dummy obligations.
     * 
     * @return
     */
    public IMarker getObMarker()
    {
        return obMarker;
    }

    /**
     * Returns the location of the obligation that was reported by tlapm.
     * Note that this is not necessarily the current location of the marker
     * representing this obligation.
     * 
     * @return
     */
    public Location getTLAPMLocation()
    {
        return location;
    }

    public String toString()
    {
        return "ID : " + id + "\nLocation : " + location + "\nStatus : " + getProverStatusString() + "\nState : "
                + obState + "\nObligation : " + obligationString;
    }
}
