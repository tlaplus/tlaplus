package org.lamport.tla.toolbox.tool.prover.ui.output.source;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.IPath;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.TLAPMData;

/**
 * Caches parsed output data from the TLAPM for use
 * by listeners that may not register until after this
 * source has received the data.
 * 
 * @author Daniel Ricketts
 *
 */
public class CachingTLAPMOutputSource implements ITLAPMOutputSource
{
    /**
     * List of objects containing
     * {@link TLAPMData} output information.
     */
    private List outputData;
    /**
     * List of listeners registered to receive TLAPM
     * output information.
     */
    private Vector listeners;
    /**
     * The full path for which this source contains
     * output.
     */
    private IPath modulePath;
    /**
     * Flag indicating that this source is done
     * receiving data.
     */
    private boolean done = false;

    public CachingTLAPMOutputSource(IPath modulePath)
    {
        listeners = new Vector();
        outputData = new LinkedList();
        this.modulePath = modulePath;
    }

    public void newData(TLAPMData data)
    {
        // cache the data for listeners added later
        outputData.add(data);

        // inform existing listeners
        for (Iterator it = listeners.iterator(); it.hasNext();)
        {
            ITLAPMOutputSourceListener listener = (ITLAPMOutputSourceListener) it.next();
            listener.newData(data);
        }
    }

    /**
     * Adds the listener to the list of listeners
     * to be notified of new data and informs the listener
     * of all existing data.
     * 
     * Does nothing if the listener is already connected
     * to this source.
     */
    public void addListener(ITLAPMOutputSourceListener listener)
    {
        if (!listeners.contains(listener))
        {
            listeners.add(listener);

            // inform the listener of data that has
            // already been added
            for (Iterator it = outputData.iterator(); it.hasNext();)
            {
                listener.newData((TLAPMData) it.next());
            }
        }
    }

    public IPath getFullModulePath()
    {
        return modulePath;
    }

    public ITLAPMOutputSourceListener[] getListeners()
    {
        return (ITLAPMOutputSourceListener[]) listeners.toArray(new ITLAPMOutputSourceListener[listeners.size()]);
    }

    public void removeListener(ITLAPMOutputSourceListener listener)
    {
        listeners.remove(listener);
    }

    public void onDone()
    {
        done = true;
    }
}
