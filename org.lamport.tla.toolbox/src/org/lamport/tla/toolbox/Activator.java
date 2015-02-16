package org.lamport.tla.toolbox;

import java.util.Iterator;
import java.util.List;
import java.util.concurrent.CountDownLatch;

import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.resources.IProject;
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
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.ui.contribution.ParseStatusContributionItem;
import org.lamport.tla.toolbox.ui.contribution.SizeControlContribution;
import org.lamport.tla.toolbox.ui.view.ProblemView;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;
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
    private ParseStatusContributionItem parseStatusContributionItem = null;
    private SizeControlContribution sizeControlContribution = null;
    
    private final Runnable parseStatusUpdateRunable = new Runnable() {

        public void run()
        {
            if (parseStatusContributionItem != null)
            {
                parseStatusContributionItem.updateStatus();
            }
        }
    };
    
    private final Runnable sizeUpdateRunnable = new Runnable() {

        public void run()
        {
            if (sizeControlContribution != null)
            {
                sizeControlContribution.updateSize();
            }
        }
    };

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
				
				specManager = new WorkspaceSpecManager();
				latch.countDown();
				return Status.OK_STATUS;
			}
        };
        initializerJob.setRule(workspace.getRuleFactory().buildRule());
        initializerJob.schedule();

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

        // install the parse status widget
        UIHelper.runUIAsync(parseStatusUpdateRunable);

        /*
         * Since the any re-parsing will update the status inside of the spec and
         * the status change is now a LifecycleEvent, there is no need of the IResourceChangeListener
         * updating the UI
        // update widget on resource modifications
        workspace.addResourceChangeListener(new IResourceChangeListener() {

            public void resourceChanged(IResourceChangeEvent event)
            {
                UIHelper.runUIAsync(parseStatusUpdateRunable);
            }
        }, IResourceChangeEvent.POST_BUILD);
        */

        // update CNF viewers
        workspace.addResourceChangeListener(new IResourceChangeListener() {

            public void resourceChanged(IResourceChangeEvent event)
            {
                ToolboxHandle.refreshToolboxExplorer();
            }
        });

        // react with window pop-up, if set up in the preferences
        workspace.addResourceChangeListener(new IResourceChangeListener() {

            private boolean hasMarkerDelta(IResourceChangeEvent event)
            {
                IMarkerDelta[] deltas = event.findMarkerDeltas(TLAMarkerHelper.TOOLBOX_MARKERS_ALL_MARKER_ID, true);
                if (deltas.length > 0)
                {
                    return true;
                }
                return false;
            }

            /* (non-Javadoc)
             * @see org.eclipse.core.resources.IResourceChangeListener#resourceChanged(org.eclipse.core.resources.IResourceChangeEvent)
             */
            public void resourceChanged(final IResourceChangeEvent event)
            {
                // no marker update
                if (!hasMarkerDelta(event))
                {
                    return;
                }

                UIHelper.runUIAsync(new Runnable() {
                    public void run()
                    {
                        boolean showProblems = PreferenceStoreHelper.getInstancePreferenceStore().getBoolean(
                                IPreferenceConstants.I_PARSER_POPUP_ERRORS);
                        if (showProblems)
                        {
                            if (TLAMarkerHelper.currentSpecHasProblems())
                            {
                                ProblemView view = (ProblemView) UIHelper.getActivePage().findView(ProblemView.ID);
                                // show
                                if (view != null)
                                {
                                    // already shown, hide
                                    UIHelper.hideView(ProblemView.ID);
                                }

                                // not shown, show
                                UIHelper.openView(ProblemView.ID);
                            } else
                            {
                                // hide
                                UIHelper.hideView(ProblemView.ID);
                            }
                        }
                    }
                });
            }
        }, IResourceChangeEvent.POST_BUILD);

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

        // Register a listener to find any changed .toobox directories of specs.
        workspace.addResourceChangeListener(new IResourceChangeListener() {

            public void resourceChanged(IResourceChangeEvent event)
            {
                IResourceDelta delta = event.getDelta();
                if (delta != null)
                {

                    ToolboxDirectoryVisitor toolboxDirectoryFinder = new ToolboxDirectoryVisitor();
                    try
                    {
                        // We cannot get the spec manager if it has not been instantiated
                        // because this would trigger a resource change event, and this code
                        // is being called within a resourceChanged method. Such an
                        // infinite loop is not allowed.
                        if (Activator.isSpecManagerInstantiated())
                        {
                            // delta.accept calls the visit method of the visitor
                            // on the delta.
                            delta.accept(toolboxDirectoryFinder);
                            List<IProject> directories = toolboxDirectoryFinder.getDirectories();
                            for (Iterator<IProject> it = directories.iterator(); it.hasNext();)
                            {   // Set resource to the IResource representing a project
                                // for a spec.  This resource is embodied in the file
                                // system as the spec's .toolbox director.
                                IProject resource = it.next();
                                ResourceHelper.setToolboxDirSize(resource);
                                
                                // TO-DO: If this is the currently opened spec, change display of
                                // that spec's size.  
                                Spec curSpec = ToolboxHandle.getCurrentSpec();
                                if ((curSpec != null) && curSpec.getProject().equals(resource)){
                                    UIHelper.runUIAsync(sizeUpdateRunnable);
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

    /**
     * This method is called by the ParseContributionItem during initialization
     */
    public void setParseStatusContribution(ParseStatusContributionItem parseStatusContributionItem)
    {
        this.parseStatusContributionItem = parseStatusContributionItem;
    }

    /**
     * Retrieves the runnable to update the Spec Parse Status Widget
     * @return
     */
    public final Runnable getParseStatusUpdateRunable()
    {
        return parseStatusUpdateRunable;
    }

    public static boolean isSpecManagerInstantiated()
    {
        return specManager != null;
    }

    public void setSizeControlContribution(SizeControlContribution sizeControlContribution)
    {
        this.sizeControlContribution = sizeControlContribution; 
        
    }
}
