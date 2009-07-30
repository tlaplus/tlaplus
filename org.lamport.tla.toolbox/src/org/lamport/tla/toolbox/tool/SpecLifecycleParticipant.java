package org.lamport.tla.toolbox.tool;

/**
 * A superclass for Spec Lifecycle Participant implementations used for 
 * registration on the <code>org.lamport.tla.toolbox.spec</code> extension point.<br />
 * This class should be overridden by the extensions.<br>
 * The overrides must provide an 0-argument constructor.
 * 
 * @see {@link SpecEvent}
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class SpecLifecycleParticipant
{
    /**
     * Marks the point in time from which on, the participant starts to receive events
     */
    public void initialize()
    {
    }

    /**
     * Is called on every spec event
     * @param event the event containing the information about what is happening
     * @return a boolean value indicating the reaction of the participant to the event. 
     * Reserved for future use.
     */
    public abstract boolean eventOccured(SpecEvent event);

    /**
     * Marks the point in time from which on, the participant stops to receive events
     */
    public void terminate()
    {
    }
}
