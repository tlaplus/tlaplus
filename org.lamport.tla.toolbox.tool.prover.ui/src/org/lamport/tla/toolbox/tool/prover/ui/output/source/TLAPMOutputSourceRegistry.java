package org.lamport.tla.toolbox.tool.prover.ui.output.source;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IPath;

/**
 * This is a singleton registry for output from the TLAPM.
 * 
 * Listeners can register themselves to receive output by calling
 * {@link TLAPMOutputSourceRegistry#addListener(ITLAPMOutputSourceListener)}.
 * Listeners that add themselves will receive all output from the most recently
 * added {@link ITLAPMOutputSource} for which {@link ITLAPMOutputSource#getFullModulePath()}
 * is equal to {@link ITLAPMOutputSourceListener#getFullModulePath()} for equality
 * computed by {@link IPath#equals(Object)}. Such a listener will also receive all future output
 * for all {@link ITLAPMOutputSource} that also meet that condition and are added to this
 * registry after the listener is added.
 * 
 * Sources implementing {@link ITLAPMOutputSource} add themselves to the registry
 * by calling {@link TLAPMOutputSourceRegistry#addSource(ITLAPMOutputSource)}.
 * 
 * The singleton instance of this class can be accessed using {@link TLAPMOutputSourceRegistry#getInstance()}.
 * 
 * @author Daniel Ricketts
 *
 */
public class TLAPMOutputSourceRegistry
{
    // singleton instance
    private static TLAPMOutputSourceRegistry instance;

    /**
     * Container for sources, hashed by {@link IPath} pointing
     * to module for that source.
     */
    private HashMap sources;

    /**
     * Map of {@link IPath} for modules to {@link List} of
     * {@link ITLAPMOutputSourceListener} for listeners
     * that have not yet been added to a source because
     * there has not been an appropriate source added to this
     * registry.
     */
    private HashMap listenerLists;

    /**
     * Adds a source to this registry. This source will replace the most
     * recently added source such that
     * 
     * existingSource.getFullModulePath().equals(newSource.getFullModulePath()).
     * 
     * @param source
     */
    public void addSource(ITLAPMOutputSource source)
    {
        /*
         * Get all listeners that should be attached to the new source.
         * 
         * First, check if there is an existing source with listeners. If not,
         * check if there are listeners that have been added but not been connected
         * to a source.
         */
        ITLAPMOutputSource existingSource = (ITLAPMOutputSource) sources.get(source.getFullModulePath());
        if (existingSource != null)
        {
            ITLAPMOutputSourceListener[] existingListeners = existingSource.getListeners();
            for (int i = 0; i < existingListeners.length; i++)
            {
                source.addListener(existingListeners[i]);
                existingSource.removeListener(existingListeners[i]);
            }
        } else
        {

            // get listeners that have not yet been added to a source
            List list = (List) listenerLists.get(source.getFullModulePath());
            if (list != null)
            {
                for (Iterator it = list.iterator(); it.hasNext();)
                {
                    source.addListener((ITLAPMOutputSourceListener) it.next());
                    it.remove();
                }
            }
        }

        // replace the existing source, if any, with the new source
        sources.put(source.getFullModulePath(), source);
    }

    /**
     * Registers the listener.
     * 
     * Listeners that add themselves will receive all output from the most recently
     * added {@link ITLAPMOutputSource} for which {@link ITLAPMOutputSource#getFullModulePath()}
     * is equal to {@link ITLAPMOutputSourceListener#getFullModulePath()} for equality
     * computed by {@link IPath#equals(Object)}. Such a listener will also receive all future output
     * for all {@link ITLAPMOutputSource} that also meet that condition and are added to this
     * registry after the listener is added.
     * 
     * @param listener
     */
    public void addListener(ITLAPMOutputSourceListener listener)
    {

        /*
         * First, check if there is an existing source to which
         * the listener should be connected. If not, add the listener
         * to the list of listeners that will be connected to a source
         * when an appropriate one is added.
         */
        ITLAPMOutputSource source = (ITLAPMOutputSource) sources.get(listener.getFullModulePath());
        if (source != null)
        {
            source.addListener(listener);
        } else
        {
            List list = (List) listenerLists.get(listener.getFullModulePath());
            if (list == null)
            {
                list = new LinkedList();
            }

            list.add(listener);
            listenerLists.put(listener.getFullModulePath(), list);
        }
    }

    /**
     * Removes the listener from any source to which it is listening and removes
     * it from listening to any sources added in the future.
     * 
     * Does nothing if the listener has not been added using {@link TLAPMOutputSourceRegistry#addListener(ITLAPMOutputSourceListener)}.
     * 
     * @param listener
     */
    public void removeListener(ITLAPMOutputSourceListener listener)
    {
        /*
         * First, try to remove the listener from a source.
         * If no source is found, remove the listener from
         * listenerLists.
         */
        ITLAPMOutputSource source = (ITLAPMOutputSource) sources.get(listener.getFullModulePath());
        if (source != null)
        {
            source.removeListener(listener);
        } else
        {
            List list = (List) listenerLists.get(listener.getFullModulePath());
            if (list != null)
            {
                list.remove(listener);
            }
        }
    }

    private TLAPMOutputSourceRegistry()
    {
        sources = new HashMap();
        listenerLists = new HashMap();
    }

    /**
     * Singleton access method.
     * @return
     */
    public static TLAPMOutputSourceRegistry getInstance()
    {
        if (instance == null)
        {
            instance = new TLAPMOutputSourceRegistry();
        }

        return instance;
    }

}
