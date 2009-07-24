package org.lamport.tla.toolbox;

import org.eclipse.core.commands.Command;
import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.commands.ICommandService;
import org.eclipse.ui.navigator.CommonNavigator;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.eclipse.ui.progress.UIJob;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.spec.parser.ParserDependencyStorage;
import org.lamport.tla.toolbox.ui.contribution.ParseStatusContributionItem;
import org.lamport.tla.toolbox.ui.handler.SwichPerspectiveHandler;
import org.lamport.tla.toolbox.ui.provider.ToolboxExplorer;
import org.lamport.tla.toolbox.ui.view.ProblemView;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class Activator extends AbstractUIPlugin
{

    // The plug-in ID
    public static final String PLUGIN_ID = "org.lamport.tla.toolbox";

    // The shared instance
    private static Activator plugin;
    private static WorkspaceSpecManager specManager;
    private static ParserDependencyStorage parserDependencyStorage;
    private ParseStatusContributionItem parseStatusContributionItem = null;

    /**
     * The constructor
     */
    public Activator()
    {
    }

    public void start(BundleContext context) throws Exception
    {
        super.start(context);
        plugin = this;

        // register the listeners
        IWorkspace workspace = ResourcesPlugin.getWorkspace();

        final Runnable parseStatusUpdateRunable = new Runnable() {

            public void run()
            {
                parseStatusContributionItem = getStatusBarContributionItem();
                if (parseStatusContributionItem != null)
                {
                    parseStatusContributionItem.updateStatus();
                }
            }
        };

        // activate handler to show the radio buttons in perspective selection 
        UIJob job = new UIJob("InitCommandsWorkaround") {
            public IStatus runInUIThread(IProgressMonitor monitor)
            {

                ICommandService commandService = (ICommandService) PlatformUI.getWorkbench().getActiveWorkbenchWindow()
                        .getService(ICommandService.class);
                Command switchPerspectiveCommand = commandService.getCommand(SwichPerspectiveHandler.COMMAND_ID);
                switchPerspectiveCommand.isEnabled();
                return new Status(IStatus.OK, PLUGIN_ID, "Init commands workaround performed succesfully");
            }

        };
        job.schedule();

        // install the parse status widget
        UIHelper.runUIAsync(parseStatusUpdateRunable);

        // update widget on resource modifications
        workspace.addResourceChangeListener(new IResourceChangeListener() {

            public void resourceChanged(IResourceChangeEvent event)
            {
                UIHelper.runUIAsync(parseStatusUpdateRunable);
            }
        }, IResourceChangeEvent.POST_BUILD);

        // update CNF viewers
        workspace.addResourceChangeListener(new IResourceChangeListener() {

            public void resourceChanged(IResourceChangeEvent event)
            {
                UIHelper.runUIAsync(new Runnable() {

                    public void run()
                    {
                        IWorkbenchPage page = UIHelper.getActivePage();
                        if (page != null)
                        {
                            IViewPart findView = UIHelper.getActivePage().findView(ToolboxExplorer.VIEW_ID);
                            if (findView != null && findView instanceof CommonNavigator)
                            {
                                ((CommonNavigator) findView).getCommonViewer().refresh();
                            }
                        }
                    }
                });
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
                });
            }
        }, IResourceChangeEvent.POST_BUILD);
    }

    public void stop(BundleContext context) throws Exception
    {
        // unregister the listeners
        specManager.terminate();
        specManager = null;
        plugin = null;

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
    public static synchronized WorkspaceSpecManager getSpecManager()
    {
        if (specManager == null)
        {
            specManager = new WorkspaceSpecManager();
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
     * Retrieve the ParseStatusContributionItem
     */
    public ParseStatusContributionItem getStatusBarContributionItem()
    {
        return this.parseStatusContributionItem;
    }

    /**
     * @param string
     * @param e
     */
    public static void logError(String message, Throwable cause)
    {
        getDefault().getLog().log(new Status(IStatus.ERROR, PLUGIN_ID, message, cause));
    }

    /**
     * @param string
     */
    public static void logDebug(String message)
    {
        getDefault().getLog().log(new Status(IStatus.INFO, PLUGIN_ID, message));        
    }

}
