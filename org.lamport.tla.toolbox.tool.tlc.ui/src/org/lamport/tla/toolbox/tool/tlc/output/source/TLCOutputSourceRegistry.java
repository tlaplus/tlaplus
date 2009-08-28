package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Enumeration;
import java.util.Hashtable;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.LogFileReader;
import org.lamport.tla.toolbox.tool.tlc.output.data.ITLCModelLaunchDataPresenter;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * A registry holding information about running processes and their status
 * The usual life cycle to work for the consumer with the registry is:
 * <ul>
 *   <li>{@link TLCOutputSourceRegistry#connect(ITLCOutputListener)}</li> 
 *   <li>The registry will call {@link ITLCOutputListener#getProcessName()} and eventually select one of the sources available</li>
 *   <li>If the source is found, {@link ITLCOutputSource#addTLCStatusListener(ITLCOutputListener)} is called passing the consumer listener instance</li>
 *   <li>After the end of the work the consumer calls {@link TLCOutputSourceRegistry#disconnect(ITLCOutputListener)}</li>
 * </ul>
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCOutputSourceRegistry
{
    private static final boolean DO_DEBUG = false;
    private static TLCOutputSourceRegistry instance;
    // container for sources, hashed by the source name
    private Hashtable sources;
    // container for data providers, hashed by the process name
    private Hashtable providers;

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
        printStats();
    }

    /**
     * Remove a source
     */
    public synchronized void removeTLCStatusSource(String name)
    {
        this.sources.remove(name);
        printStats();
    }

    /**
     * Connect the source to the listener
     * @return 
     */
    public synchronized boolean connect(ITLCOutputListener listener)
    {
        Assert.isNotNull(listener);

        String processName = listener.getProcessName();
        ITLCOutputSource source = (ITLCOutputSource) this.sources.get(processName);
        if (source == null)
        {
            ILaunchConfiguration config = ModelHelper.getModelByName(processName);
            IFile logFile = ModelHelper.getModelOutputLogFile(config);
            if (logFile != null && logFile.exists())
            {
                // initialize the reader and read the content
                LogFileReader logFileReader = new LogFileReader(processName, logFile);
                logFileReader.read();

                source = logFileReader.getSource();

                // the reader should have added a new source
                // query for it
                source.addTLCStatusListener(listener);
                Assert.isTrue((ITLCOutputSource) this.sources.get(processName) != null);
            } else
            {
                TLCUIActivator.logDebug("No source for " + processName + " found.");
                return false;
            }

        } else
        {
            source.addTLCStatusListener(listener);
        }

        // TLCUIActivator.logDebug("Connected " + source.getListeners().length + " listeners");
        printStats();
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

        printStats();
    }

    public void startProcess(ILaunchConfiguration config)
    {
        TLCModelLaunchDataProvider provider = new TLCModelLaunchDataProvider(config);
        providers.put(provider.getProcessName(), provider);
    }

    /**
     * Retrieves the data provider for the given process
     * @return
     */
    public synchronized TLCModelLaunchDataProvider getProvider(ITLCModelLaunchDataPresenter presenter)
    {
        Assert.isNotNull(presenter);
        String processKey = presenter.getConfig().getFile().getName();
        TLCModelLaunchDataProvider provider = (TLCModelLaunchDataProvider) providers.get(processKey);
        if (provider != null)
        {
            provider.setPresenter(presenter);
        }
        return provider;
    }

    /**
     * Clients should not invoke this constructor directly, but use {@link TLCOutputSourceRegistry#getStatusRegistry()} instead
     */
    private TLCOutputSourceRegistry()
    {
        this.sources = new Hashtable();
        this.providers = new Hashtable();
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

    /**
     * Debugging
     */
    private void printStats()
    {
        if (DO_DEBUG)
        {
            TLCUIActivator.logDebug("TLCOutputSourceRegistry maintains " + sources.size() + " sources.");
            Enumeration keys = sources.keys();
            while (keys.hasMoreElements())
            {
                String sourceName = (String) keys.nextElement();
                ITLCOutputSource source = (ITLCOutputSource) sources.get(sourceName);
                TLCUIActivator.logDebug("The source " + sourceName + " has " + source.getSourcePrio() + " prio and "
                        + source.getListeners().length + " listeners");

            }
        }
    }
}
