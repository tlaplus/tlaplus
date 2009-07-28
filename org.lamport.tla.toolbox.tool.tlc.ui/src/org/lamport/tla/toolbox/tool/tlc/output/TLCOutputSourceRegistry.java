package org.lamport.tla.toolbox.tool.tlc.output;

import java.util.Hashtable;

import org.eclipse.core.runtime.Assert;

/**
 * A registry holding information about running processes and their status
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCOutputSourceRegistry
{
    private static TLCOutputSourceRegistry instance;
    private Hashtable sources;

    /**
     * Adds a source
     */
    public void addTLCStatusSource(ITLCOutputSource source, String name)
    {
        this.sources.put(name, source);
    }

    /**
     * Remove a source
     */
    public void removeTLCStatusSource(String name)
    {
        this.sources.remove(name);
    }

    /**
     * Connect the source to the listener
     */
    public void connect(ITLCOutputListener listener)
    {
        Assert.isNotNull(listener);

        ITLCOutputSource source = (ITLCOutputSource) this.sources.get(listener.getProcessName());
        if (source == null)
        {
            // TODO lookup if another source can be constructed
            // put it into the list of sources
            System.out.println("No source for " + listener.getProcessName() + " found.");
        } else
        {
            source.addTLCStatusListener(listener);
        }
    }

    /**
     * Disconnect the source from the listener
     */
    public void disconnect(ITLCOutputListener listener)
    {
        Assert.isNotNull(listener);

        ITLCOutputSource source = (ITLCOutputSource) this.sources.get(listener.getProcessName());
        if (source != null)
        {
            source.removeTLCStatusListener(listener);
        }
    }

    /**
     * Clients should not invoke this constructor directly, but use {@link TLCOutputSourceRegistry#getStatusRegistry()} instead
     */
    private TLCOutputSourceRegistry()
    {
        this.sources = new Hashtable();
    }

    /**
     * Factory method
     * @return
     */
    public static TLCOutputSourceRegistry getStatusRegistry()
    {
        if (instance == null)
        {
            instance = new TLCOutputSourceRegistry();
        }
        return instance;
    }

}
