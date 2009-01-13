package org.lamport.tla.toolbox.spec.manager;

import java.util.Vector;

/**
 * Abstract spec manager
 * @author zambrovski
 */
public abstract class AbstractSpecManager implements ISpecManager
{

    protected Vector listeners = new Vector();

    /* (Non-JavaDoc)
     * @see ISpecManager#addSpecManagerListener(SpecManagerListener)
     */
    public void addSpecManagerListener(SpecManagerListener l)
    {
        listeners.add(l);
    }
    /* (Non-JavaDoc)
     * @see ISpecManager#removeSpecManagerListener(SpecManagerListener)
     */
    public void removeSpecManagerListener(SpecManagerListener l)
    {
        listeners.remove(l);
    }

    /**
     * Notify the changes to the listeners
     */
    public void notifyChanges(SpecManagerEvent e)
    {

        for (int i = 0; i < listeners.size(); i++)
        {
            ((SpecManagerListener) listeners.elementAt(i)).specManagerChanges(e);
        }
    }
}
