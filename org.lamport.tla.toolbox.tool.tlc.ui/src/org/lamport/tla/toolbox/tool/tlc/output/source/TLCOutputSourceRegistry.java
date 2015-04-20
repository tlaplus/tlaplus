package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Enumeration;
import java.util.Hashtable;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.LogFileReader;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.data.TraceExplorerDataProvider;
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
 *   <li>If the source is selected, {@link ITLCOutputSource#addTLCOutputListener(ITLCOutputListener)} is called by the registry on it, 
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
 * There should be at most two instances of this class, one for output sources from running TLC for model checking and one for running TLC
 * for trace exploration. The flag isTraceExploreInstance indicates which type of instance it is, and the methods
 * {@link TLCOutputSourceRegistry#getModelCheckSourceRegistry()} and {@link TLCOutputSourceRegistry#getTraceExploreSourceRegistry()}
 * provide access to each instance.
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCOutputSourceRegistry
{
    private static final boolean DO_DEBUG = true;
    // instance for output sources from model checking
    private static TLCOutputSourceRegistry modelCheckInstance;
    // instance for output sources from trace exploration
    private static TLCOutputSourceRegistry traceExploreInstance;
    // container for sources, hashed by the source name
    private Hashtable<String, ITLCOutputSource> sources;
    // container for data providers, hashed by the process name
    private Hashtable<String, TLCModelLaunchDataProvider> providers;
    // flag indicating if this is a trace explorer instance
    // true indicates that this is a trace explorer instance
    private boolean isTraceExploreInstance;

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

        // TLCUIActivator.getDefault().logDebug("adding source " + source.getSourceName() + " " + source.getSourcePrio());

        ITLCOutputSource existingSource = this.sources.get(source.getTLCOutputName());

        // a new source for a given name arrives which has a higher priority
        // re-register the listeners
        if (existingSource != null && source.getSourcePrio() >= existingSource.getSourcePrio())
        {
            ITLCOutputListener[] registered = existingSource.getListeners();
            for (int i = 0; i < registered.length; i++)
            {
                existingSource.removeTLCOutputListener(registered[i]);
                source.addTLCOutputListener(registered[i]);
                registered[i].onNewSource();
            }
        } else
        {
            if (existingSource == null)
            {
                // the source didn't exist, but there is a data provider interested in this source
                TLCModelLaunchDataProvider provider = providers.get(source
                        .getTLCOutputName());
                if (provider != null)
                {
                    source.addTLCOutputListener(provider);
                }
            }
        }
        this.sources.put(source.getTLCOutputName(), source);

        printStats();
    }

    /**
     * Remove a source and the date provider associated with that source, if it
     * exists.
     */
    private synchronized void removeTLCStatusSource(ILaunchConfiguration ilc)
    {
    	String name = ilc.getFile().getName();
        this.sources.remove(name);
        this.providers.remove(name);
        printStats();
    }

    /**
     * Remove a source and the date provider associated with that source, if it
     * exists.
     */
    public synchronized void removeTLCStatusSource(ILaunchConfiguration[] ilcs)
    {
    	for (int i = 0; i < ilcs.length; i++) {
			removeTLCStatusSource(ilcs[i]);
		}
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
        ITLCOutputSource source = this.sources.get(processName);
        if (source == null)
        {
            // no source found, so no live TLC process
            // also not a source for trace explorer output, so
            // can look for the log file
            ILaunchConfiguration config = ModelHelper.getModelByName(processName);
            if (config == null) {
				// Config can be null after startup following a hard crash when
				// the Toolbox restores the ModelEditor but no spec is currently
				// open/loaded. In this case fail gracefully rather than hang
				// the Toolbox.
            	return false;
            }
            IFile logFile = ModelHelper.getModelOutputLogFile(config, isTraceExploreInstance);
            // log file found
            if (logFile != null && logFile.exists())
            {
                // initialize the reader and read the content
                // this will create the parser
                // the parser will create a source and register in the registry
                LogFileReader logFileReader = new LogFileReader(processName, logFile, isTraceExploreInstance);

                // retrieve the source
                source = logFileReader.getSource();
                source.addTLCOutputListener(listener);

                // read in the data
                logFileReader.read();

                // from now on we should have a source for this model
                Assert.isTrue(this.sources.get(processName) != null);
            } else
            {
                // no log file
                if (DO_DEBUG)
                {
                    TLCUIActivator.getDefault().logDebug("No source for " + processName + " found.");
                }
                return false;
            }

        } else
        {
            source.addTLCOutputListener(listener);
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

        ITLCOutputSource source = this.sources.get(listener.getTLCOutputName());
        if (source != null)
        {
            source.removeTLCOutputListener(listener);
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
        TLCModelLaunchDataProvider provider = providers.get(processKey);
        if (provider == null)
        {
            if (isTraceExploreInstance)
            {
                provider = new TraceExplorerDataProvider(configuration);
            } else
            {
                provider = new TLCModelLaunchDataProvider(configuration);
            }
            providers.put(processKey, provider);
        }
        return provider;
    }

    /**
     * Clients should not invoke this constructor directly, but use {@link TLCOutputSourceRegistry#getModelCheckSourceRegistry()}
     * or {@link TLCOutputSourceRegistry#getTraceExploreSourceRegistry()} instead.
     */
    private TLCOutputSourceRegistry()
    {
        this.sources = new Hashtable<String, ITLCOutputSource>();
        this.providers = new Hashtable<String, TLCModelLaunchDataProvider>();
    }

    /**
     * Access method for model check source registry instance
     * @return a working copy of the registry
     */
    public static TLCOutputSourceRegistry getModelCheckSourceRegistry()
    {
        if (modelCheckInstance == null)
        {
            modelCheckInstance = new TLCOutputSourceRegistry();
            modelCheckInstance.isTraceExploreInstance = false;
        }
        return modelCheckInstance;
    }

    /**
     * Access method for trace explore source registry instance
     */
    public static TLCOutputSourceRegistry getTraceExploreSourceRegistry()
    {
        if (traceExploreInstance == null)
        {
            traceExploreInstance = new TLCOutputSourceRegistry();
            traceExploreInstance.isTraceExploreInstance = true;
        }
        return traceExploreInstance;
    }

    /**
     * Debugging
     */
    private void printStats()
    {
        if (DO_DEBUG)
        {
            String type = "model checking";
            if (isTraceExploreInstance)
            {
                type = "trace exploration";
            }
            TLCUIActivator.getDefault().logDebug("TLCOutputSourceRegistry for " + type + " maintains " + sources.size()
                    + " sources.");
            Enumeration<String> keys = sources.keys();
            while (keys.hasMoreElements())
            {
                String sourceName = keys.nextElement();
                ITLCOutputSource source = sources.get(sourceName);
                TLCUIActivator.getDefault().logDebug("The source " + sourceName + " has " + source.getSourcePrio() + " prio and "
                        + source.getListeners().length + " listeners");

            }
        }
    }
}
