package org.lamport.tla.toolbox.ui.contribution;

import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Updates the Parse status widget on any spec operations
 * @author Simon Zambrovski
 * @version $Id$
 */
public class StatusReflectingSpecLifecycleParticipant extends SpecLifecycleParticipant
{

    private Runnable parseStatusUpdateRunable;

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.SpecLifecycleParticipant#eventOccured(org.lamport.tla.toolbox.tool.SpecEvent)
     */
    public void initialize()
    {
        parseStatusUpdateRunable = Activator.getDefault().getParseStatusUpdateRunable();
    }

    public void terminate()
    {
        parseStatusUpdateRunable = null;
    }

    /*
     * Update the widget on spec operations
     * @see org.lamport.tla.toolbox.tool.SpecLifecycleParticipant#eventOccured(org.lamport.tla.toolbox.tool.SpecEvent)
     */
    public boolean eventOccured(SpecEvent event)
    {
        UIHelper.runUIAsync(parseStatusUpdateRunable);
        return true;
    }

}
