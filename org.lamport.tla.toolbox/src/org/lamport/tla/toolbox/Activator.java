package org.lamport.tla.toolbox;

import java.util.concurrent.CountDownLatch;

import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.spec.nature.TLAParsingBuilder.OutOfBuildSpecModulesGatheringDeltaVisitor;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.ParserDependencyStorage;
import org.osgi.framework.Bundle;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractTLCActivator
{

    // The plug-in ID
    public static final String PLUGIN_ID = "org.lamport.tla.toolbox";

    // The shared instance
    private static Activator plugin;
    private static WorkspaceSpecManager specManager;
    private static final CountDownLatch latch = new CountDownLatch(1);
    private static ParserDependencyStorage parserDependencyStorage;

    /**
     * The constructor
     */
    public Activator()
    {
    	super(PLUGIN_ID);
    }

    public void start(final BundleContext context) throws Exception
    {
        super.start(context);
        plugin = this;

        // register the listeners
        IWorkspace workspace = ResourcesPlugin.getWorkspace();
        
		// Eagerly initialize the WorkspaceSpecManager to prevent a possible
		// deadlock among threads (including main) that arises if jobs get
		// scheduled and try to lazily access the WorkspaceSpecManager which -in
		// turn- hasn't been initialized yet but locked by another thread.
        //
		// At this point, it can safely be assumed that no build job is running,
        // because we schedule prior to loading the TLAParserBuilder class.
        //
		// Using a WorkspaceJob instead of a "normal" Job makes sure the
		// operation is executed atomically.
        //
		// We do this in a separate thread and not in Activator.start() because
		// the OSGi contract requires for short-running bundle activation
		// (start/stop) methods. Initializing the WorkspaceSpecManager involves
		// I/O though, which makes it a potentially long-running task.
        //
        // @see https://bugzilla.tlaplus.net/show_bug.cgi?id=260
        final Job initializerJob = new WorkspaceJob("Initializing workspace...") {
			/* (non-Javadoc)
			 * @see org.eclipse.core.resources.WorkspaceJob#runInWorkspace(org.eclipse.core.runtime.IProgressMonitor)
			 */
			public IStatus runInWorkspace(IProgressMonitor monitor)
					throws CoreException {
				
				// Wait until bundle is done starting up and we can safely
				// load classes in this thread
				int state = context.getBundle().getState();
				while(state != Bundle.ACTIVE && state != Bundle.RESOLVED) {
					// Do not yield the job because we would potentially give
					// away the lock to the autobuilder job which would then get
					// stuck on the latch we are supposed to take down.
					try {
						synchronized(getThread()) {
							getThread().wait(100);
						}
					} catch (InterruptedException e) {
						e.printStackTrace();
					}
					state = context.getBundle().getState();
				}
				
				specManager = new WorkspaceSpecManager(monitor);
				latch.countDown();
				return Status.OK_STATUS;
			}
        };
        initializerJob.setRule(workspace.getRuleFactory().buildRule());
        initializerJob.schedule();
        
		// Running plug-in tests with Eclipse 4.5, the foundation suspends the
		// JobManager at startup causing our jobs to never be executed. In turn,
		// this causes the Toolbox to hang at startup. Thus, resume the JobManager
        // which is a no-op outside the test mode.
        Job.getJobManager().resume();

        // activate handler to show the radio buttons in perspective selection
        // UIJob job = new UIJob("InitCommandsWorkaround") {
        // public IStatus runInUIThread(IProgressMonitor monitor)
        // {
        //
        // ICommandService commandService = (ICommandService) PlatformUI.getWorkbench().getActiveWorkbenchWindow()
        // .getService(ICommandService.class);
        // Command switchPerspectiveCommand = commandService.getCommand(SwitchPerspectiveHandler.COMMAND_ID);
        // switchPerspectiveCommand.isEnabled();
        // return new Status(IStatus.OK, PLUGIN_ID, "Init commands workaround performed succesfully");
        // }
        //
        // };
        // job.schedule();

        workspace.addResourceChangeListener(new IResourceChangeListener() {

            public void resourceChanged(IResourceChangeEvent event)
            {
                IResourceDelta delta = event.getDelta();
                if (delta != null)
                {

                    OutOfBuildSpecModulesGatheringDeltaVisitor moduleFinder = new OutOfBuildSpecModulesGatheringDeltaVisitor();
                    try
                    {
                        // We cannot get the spec manager if it has not been instantiated
                        // because this would trigger a resource change event, and this code
                        // is being called within a resourceChanged method. Such an
                        // infinite loop is not allowed.
                        if (Activator.isSpecManagerInstantiated())
                        {
                            delta.accept(moduleFinder);
                            if (!moduleFinder.getModules().isEmpty())
                            {
                                Spec spec = getSpecManager().getSpecLoaded();
                                if (spec != null)
                                {
                                    spec.setStatus(IParseConstants.UNPARSED);
                                }
                            }
                        }
                    } catch (CoreException e)
                    {
                        Activator.getDefault().logError("Error during post save status update", e);
                    }
                }

            }

        }, IResourceChangeEvent.POST_CHANGE);
    }

    public void stop(BundleContext context) throws Exception
    {
        // unregister the listeners
    	if (specManager != null)
    		specManager.terminate();
        
		// do not null specManager and plugin to let backend jobs finish cleanly
        //
        // remember: Nulling specManager might cause the initialization of a new
        // specManager object during shutdown if this method nulls it and subsequent
        // calls to getSpecManager() occur. This might potentially leave an inconsistent 
        // spec manager on which terminate() might never be called.

//        specManager = null;
//        plugin = null;

    	// In case of a clean shutdown explicitly do a *full* workspace save. If omitted,
    	// the Eclipse foundation's default is to just trigger a *snapshot* save.
    	// The default snapshot save is apparently insufficient when the Eclipse foundation
    	// itself gets updated to a newer version (from 3.x to 4.x in the current case)
    	// (The assumption being that the on-disk format of the *.snap files changed causing 
    	// a subsequent startup to crash the whole Toolbox). 
    	final IWorkspace workspace = ResourcesPlugin.getWorkspace();
        final Job saveJob = new WorkspaceJob("Saving workspace...") {
			/* (non-Javadoc)
			 * @see org.eclipse.core.resources.WorkspaceJob#runInWorkspace(org.eclipse.core.runtime.IProgressMonitor)
			 */
			public IStatus runInWorkspace(final IProgressMonitor monitor)
					throws CoreException {
		        return workspace.save(true, monitor);
			}
        };
        saveJob.setRule(workspace.getRuleFactory().buildRule());
        saveJob.schedule();
    	
        super.stop(context);
    }

    /**
     * Returns the shared instance
     *
     * @return the shared instance
     */
    public static Activator getDefault()
    {
        return plugin;
    }

	/**
	 * Retrieves a working spec manager instance
	 */
	public static WorkspaceSpecManager getSpecManager() {
		try {
			latch.await();
		} catch (InterruptedException e) {
			// shall never happen
			e.printStackTrace();
			return null;
		}
		return specManager;
	}
    
    /**
     * Retrieves a working instance of parser dependency storage
     */
    public static synchronized ParserDependencyStorage getModuleDependencyStorage()
    {
        if (parserDependencyStorage == null)
        {
            parserDependencyStorage = new ParserDependencyStorage();
        }
        return parserDependencyStorage;
    }

    public static boolean isSpecManagerInstantiated()
    {
        return specManager != null;
    }
}
