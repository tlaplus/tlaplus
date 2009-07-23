package org.lamport.tla.toolbox.tool;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class SpecLifecycleParticipant
{
    public void initialize()
    {
    }

    public abstract boolean eventOccured(SpecEvent event);
    

    public void terminate()
    {
    }
}
