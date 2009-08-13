package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Hashtable;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.LogFileReader;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * A registry holding information about running processes and their status
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCOutputSourceRegistry
{
    private static TLCOutputSourceRegistry instance;
    // container for sources, hashed by the source name
    private Hashtable sources;

    /**
     * Adds a source
     */
    public synchronized void addTLCStatusSource(ITLCOutputSource source)
    {
        Assert.isNotNull(source);
        
        // TLCUIActivator.logDebug("adding source " + source.getSourceName() + " " + source.getSourcePrio());

        ITLCOutputSource existingSource = (ITLCOutputSource) this.sources.get(source.getSourceName());

        // a new source for a given name arrives which has a higher priority
        // re-register the listeners
        if (existingSource != null && source.getSourcePrio() > existingSource.getSourcePrio())
        {
            ITLCOutputListener[] registered = existingSource.getListeners();
            for (int i = 0; i < registered.length; i++)
            {
                existingSource.removeTLCStatusListener(registered[i]);
                source.addTLCStatusListener(registered[i]);
                registered[i].onNewSource();
            }
        }
        this.sources.put(source.getSourceName(), source);
    }

    /**
     * Remove a source
     */
    public synchronized void removeTLCStatusSource(String name)
    {
        this.sources.remove(name);
    }

    /**
     * Connect the source to the listener
     * @return 
     */
    public synchronized boolean connect(ITLCOutputListener listener)
    {
        Assert.isNotNull(listener);

        ITLCOutputSource source = (ITLCOutputSource) this.sources.get(listener.getProcessName());
        if (source == null)
        {
            ILaunchConfiguration config = ModelHelper.getModelByName(listener.getProcessName());
            IFile logFile = ModelHelper.getModelOutputLogFile(config);
            if (logFile != null && logFile.exists())
            {
                // initialize the reader and read the content
                LogFileReader logFileReader = new LogFileReader(listener.getProcessName(), logFile);
                logFileReader.read();

                source = logFileReader.getSource();

                // the reader should have added a new source
                // query for it

                Assert.isTrue((ITLCOutputSource) this.sources.get(listener.getProcessName()) != null);
            } else
            {
                TLCUIActivator.logDebug("No source for " + listener.getProcessName() + " found.");
                return false;
            }

        } else
        {
            source.addTLCStatusListener(listener);
        }

        // TLCUIActivator.logDebug("Connected " + source.getListeners().length + " listeners");
        return true;
    }

    /**
     * Disconnect the source from the listener
     */
    public synchronized void disconnect(ITLCOutputListener listener)
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
