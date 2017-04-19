package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.ui.progress.IProgressConstants;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.ITLCOutputListener;
import org.lamport.tla.toolbox.tool.tlc.output.LogFileReader;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.data.TraceExplorerDataProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

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
 *   <li>The registry will call {@link ITLCOutputListener#getModel()} and eventually select among one of the sources available</li>
 *   <li>If the source is selected, {@link ITLCOutputSource#addTLCOutputListener(ITLCOutputListener)} is called by the registry on it, 
 *   passing the consumer listener instance</li>
 *   <li>After the end of the with the source, the consumer is disconnected by calling {@link TLCOutputSourceRegistry#disconnect(ITLCOutputListener)}</li>
 * </ul>
 * <br><br>
 * A new source of the TLC output is added by calling {@link TLCOutputSourceRegistry#addTLCOutputSource(ITLCOutputSource)} method. The source 
 * is identified by the name and priority. The methods {@link ITLCOutputSource#getModel()} and {@link ITLCOutputSource#getSourcePrio()}
 * are used to obtain this information. If any listener have been registered, which are interested in the certain TLC Output (the values of 
 * {@link ITLCOutputListener#getModel()} and {@link ITLCOutputSource#getModel()}) are equal, then these will be registered by the
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
    private static final boolean DO_DEBUG = Boolean.getBoolean(TLCOutputSourceRegistry.class.getName() + ".debug");
    // instance for output sources from model checking
    private static TLCOutputSourceRegistry modelCheckInstance;
    // instance for output sources from trace exploration
    private static TLCOutputSourceRegistry traceExploreInstance;
    // container for sources, hashed by the source name
    private Map<Model, ITLCOutputSource> sources;
    // container for data providers, hashed by the process name
    private Map<Model, TLCModelLaunchDataProvider> providers;
    // flag indicating if this is a trace explorer instance
    // true indicates that this is a trace explorer instance
    private boolean isTraceExploreInstance;

    /**
     * Adds a source. If the source with the same identity is already present,
     * reconnect the the listeners, iff there are any at place and the prio of the new source is higher
     * that the one of the old one.
     * @param source new source
     * @see ITLCOutputSource#getModel()
     * @see ITLCOutputSource#getSourcePrio()
     */
    public synchronized void addTLCOutputSource(ITLCOutputSource source)
    {
        Assert.isNotNull(source);

        // TLCUIActivator.getDefault().logDebug("adding source " + source.getSourceName() + " " + source.getSourcePrio());

        ITLCOutputSource existingSource = this.sources.get(source.getModel());

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
                        .getModel());
                if (provider != null)
                {
                    source.addTLCOutputListener(provider);
                }
            }
        }
        this.sources.put(source.getModel(), source);

        printStats();
    }

    /**
     * Remove a source and the date provider associated with that source, if it
     * exists.
     */
    private synchronized void removeTLCStatusSource(Model model)
    {
        this.sources.remove(model);
        this.providers.remove(model);
        printStats();
    }
    
    /**
     * Remove a source and the date provider associated with that source, if it
     * exists.
     */
    public synchronized void removeTLCStatusSource(Model[] models)
    {
    	for (int i = 0; i < models.length; i++) {
			removeTLCStatusSource(models[i]);
		}
    }

    /**
     * Connect the source to the listener
     * @param an instance of ITLCOutputListener interested in the receiving of TLC output from source 
     * with {@link ITLCOutputSource#getModel()} equals to {@link ITLCOutputListener#getModel()}  
     * @return status of connection: <code>true</code> if successfully connected, <code>false</code> otherwise
     */
    public synchronized boolean connect(ITLCOutputListener listener)
    {
        Assert.isNotNull(listener);
        Model model = listener.getModel();

        // try to obtain a source
        ITLCOutputSource source = this.sources.get(model);
        if (source == null)
        {
            // no source found, so no live TLC process
            // also not a source for trace explorer output, so
            // can look for the log file
            if (model == null) {
				// Config can be null after startup following a hard crash when
				// the Toolbox restores the ModelEditor but no spec is currently
				// open/loaded. In this case fail gracefully rather than hang
				// the Toolbox.
            	return false;
            }
            IFile logFile = model.getOutputLogFile(isTraceExploreInstance);
            // log file found
            if (logFile != null && logFile.exists())
            {
                // initialize the reader and read the content
                // this will create the parser
                // the parser will create a source and register in the registry
                final LogFileReader logFileReader = new LogFileReader(model, logFile, isTraceExploreInstance);

                // retrieve the source
                source = logFileReader.getSource();
                source.addTLCOutputListener(listener);

                // read in the data
                // read in the data
                final Job job = new WorkspaceJob("Logfile reader...") {
					public IStatus runInWorkspace(IProgressMonitor monitor) throws CoreException {
						try {
							logFileReader.read(monitor);
						} catch (BadLocationException e) {
							return new Status(IStatus.ERROR, Activator.PLUGIN_ID, e.getMessage());
						} catch (IOException e) {
							return new Status(IStatus.ERROR, Activator.PLUGIN_ID, e.getMessage());
						}
						return Status.OK_STATUS;
					}
				};
				job.setProperty(IProgressConstants.PROPERTY_IN_DIALOG, true);
				job.setPriority(Job.LONG);
				job.setUser(true);
				job.schedule();

                // from now on we should have a source for this model
                Assert.isTrue(this.sources.get(model) != null);
            } else
            {
                // no log file
                if (DO_DEBUG)
                {
                    TLCUIActivator.getDefault().logDebug("No source for " + model.getName() + " found.");
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

        ITLCOutputSource source = this.sources.get(listener.getModel());
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
    public synchronized TLCModelLaunchDataProvider getProvider(Model model)
    {
        Assert.isNotNull(model);
        TLCModelLaunchDataProvider provider = providers.get(model);
        if (provider == null)
        {
            if (isTraceExploreInstance)
            {
                provider = new TraceExplorerDataProvider(model);
            } else
            {
                provider = new TLCModelLaunchDataProvider(model);
            }
            providers.put(model, provider);
        }
        return provider;
    }

    /**
     * Clients should not invoke this constructor directly, but use {@link TLCOutputSourceRegistry#getModelCheckSourceRegistry()}
     * or {@link TLCOutputSourceRegistry#getTraceExploreSourceRegistry()} instead.
     */
    private TLCOutputSourceRegistry()
    {
        this.sources = new HashMap<Model, ITLCOutputSource>();
        this.providers = new HashMap<Model, TLCModelLaunchDataProvider>();
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
            Set<Model> keySet = sources.keySet();
            for (Model model : keySet) {
            	ITLCOutputSource source = sources.get(model);
            	TLCUIActivator.getDefault().logDebug("The source " + model.getName() + " has " + source.getSourcePrio() + " prio and "
            			+ source.getListeners().length + " listeners");
			}
        }
    }
}
