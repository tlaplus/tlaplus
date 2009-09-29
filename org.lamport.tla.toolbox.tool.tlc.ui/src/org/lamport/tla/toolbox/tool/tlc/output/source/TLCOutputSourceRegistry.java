package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Enumeration;
import java.util.Hashtable;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.LogFileReader;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * The TLC process can produce some output, which needs to be processed by a consumer. The TLC Output Source ({@link ITLCOutputSource})
 * is the abstract representation of the source of the output. In order to process the output from the source, the TLC Output
 * listener is introduced ({@link ITLCOutputListener}). One source can have multiple listeners, and there can be several sources
 * of the output for launches of the same model over time. 
 * <br><br>
 * The consumer of the output must implement the {@link ITLCOutputListener} interface. Its instance has the following life cycle 
 * during the work with the registry:
 * <ul>
 *   <li>The consumer is passed as to the registry during the call of {@link TLCOutputSourceRegistry#connect(ITLCOutputListener)}</li> 
 *   <li>The registry will call {@link ITLCOutputListener#getTLCOutputName()} and eventually select among one of the sources available</li>
 *   <li>If the source is selected, {@link ITLCOutputSource#addTLCStatusListener(ITLCOutputListener)} is called by the registry on it, 
 *   passing the consumer listener instance</li>
 *   <li>After the end of the with the source, the consumer is disconnected by calling {@link TLCOutputSourceRegistry#disconnect(ITLCOutputListener)}</li>
 * </ul>
 * <br><br>
 * A new source of the TLC output is added by calling {@link TLCOutputSourceRegistry#addTLCOutputSource(ITLCOutputSource)} method. The source 
 * is identified by the name and priority. The methods {@link ITLCOutputSource#getTLCOutputName()} and {@link ITLCOutputSource#getSourcePrio()}
 * are used to obtain this information. If any listener have been registered, which are interested in the certain TLC Output (the values of 
 * {@link ITLCOutputListener#getTLCOutputName()} and {@link ITLCOutputSource#getTLCOutputName()}) are equal, then these will be registered by the
 * new source. The priority resolves the case if a new source for the same name arrives. Currently, high priority is used for the source attached
 * to the running process, low priority is used for the file source. 
 * 
 * 
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCOutputSourceRegistry
{
    private static final boolean DO_DEBUG = true;
    private static TLCOutputSourceRegistry instance;
    // container for sources, hashed by the source name
    private Hashtable sources;
    // container for data providers, hashed by the process name
    private Hashtable providers;

    /**
     * Adds a source. If the source with the same identity is already present,
     * reconnect the the listeners, iff there are any at place and the prio of the new source is higher
     * that the one of the old one.
     * @param source new source
     * @see ITLCOutputSource#getTLCOutputName()
     * @see ITLCOutputSource#getSourcePrio()
     */
    public synchronized void addTLCOutputSource(ITLCOutputSource source)
    {
        Assert.isNotNull(source);

        // TLCUIActivator.logDebug("adding source " + source.getSourceName() + " " + source.getSourcePrio());

        ITLCOutputSource existingSource = (ITLCOutputSource) this.sources.get(source.getTLCOutputName());

        // a new source for a given name arrives which has a higher priority
        // re-register the listeners
        if (existingSource != null && source.getSourcePrio() >= existingSource.getSourcePrio())
        {
            ITLCOutputListener[] registered = existingSource.getListeners();
            for (int i = 0; i < registered.length; i++)
            {
                existingSource.removeTLCStatusListener(registered[i]);
                source.addTLCStatusListener(registered[i]);
                registered[i].onNewSource();
            }
        } else 
        {
            if (existingSource == null) 
            {
                // the source didn't exist, but there is a data provider interested in this source
                TLCModelLaunchDataProvider provider = (TLCModelLaunchDataProvider) providers.get(source.getTLCOutputName());
                if (provider != null) 
                {
                    source.addTLCStatusListener(provider);
                }
            }
        }
        this.sources.put(source.getTLCOutputName(), source);
        
        
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
     * @param an instance of ITLCOutputListener interested in the receiving of TLC output from source 
     * with {@link ITLCOutputSource#getTLCOutputName()} equals to {@link ITLCOutputListener#getTLCOutputName()}  
     * @return status of connection: <code>true</code> if successfully connected, <code>false</code> otherwise
     */
    public synchronized boolean connect(ITLCOutputListener listener)
    {
        Assert.isNotNull(listener);
        String processName = listener.getTLCOutputName();

        // try to obtain a source
        ITLCOutputSource source = (ITLCOutputSource) this.sources.get(processName);
        if (source == null)
        {
            // no source found, so no live TLC process
            // look for the log file
            ILaunchConfiguration config = ModelHelper.getModelByName(processName);
            IFile logFile = ModelHelper.getModelOutputLogFile(config);
            // log file found
            if (logFile != null && logFile.exists())
            {
                // initialize the reader and read the content
                // this will create the parser
                // the parser will create a source and register in the registry
                LogFileReader logFileReader = new LogFileReader(processName, logFile);

                // retrieve the source
                source = logFileReader.getSource();
                source.addTLCStatusListener(listener);

                // read in the data
                logFileReader.read();

                // from now on we should have a source for this model
                Assert.isTrue((ITLCOutputSource) this.sources.get(processName) != null);
            } else
            {
                // no log file
                if (DO_DEBUG)
                {
                    TLCUIActivator.logDebug("No source for " + processName + " found.");
                }
                return false;
            }

        } else
        {
            source.addTLCStatusListener(listener);
        }

        printStats();
        return true;
    }

    /**
     * Disconnect the source from the listener
     */
    public synchronized void disconnect(ITLCOutputListener listener)
    {
        Assert.isNotNull(listener);

        ITLCOutputSource source = (ITLCOutputSource) this.sources.get(listener.getTLCOutputName());
        if (source != null)
        {
            source.removeTLCStatusListener(listener);
        }

        printStats();
    }

    /**
     * Retrieves the data provider for the given configuration
     * @return a data provider for the current model
     */
    public synchronized TLCModelLaunchDataProvider getProvider(ILaunchConfiguration configuration)
    {
        Assert.isNotNull(configuration);
        String processKey = configuration.getFile().getName();
        TLCModelLaunchDataProvider provider = (TLCModelLaunchDataProvider) providers.get(processKey);
        if (provider == null) 
        {
            provider = new TLCModelLaunchDataProvider(configuration);
            providers.put(processKey, provider);
        }
        return provider;
    }

    /**
     * Clients should not invoke this constructor directly, but use {@link TLCOutputSourceRegistry#getSourceRegistry()} instead
     */
    private TLCOutputSourceRegistry()
    {
        this.sources = new Hashtable();
        this.providers = new Hashtable();
    }

    /**
     * Singleton access method
     * @return a working copy of the registry
     */
    public static TLCOutputSourceRegistry getSourceRegistry()
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
