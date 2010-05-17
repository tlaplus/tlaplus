package org.lamport.tla.toolbox.tool.prover.ui;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.lamport.tla.toolbox.tool.prover.ui.view.ObligationsView;
import org.lamport.tla.toolbox.tool.prover.util.ProverHelper;
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class ProverUIActivator extends AbstractUIPlugin
{

    // The plug-in ID
    public static final String PLUGIN_ID = "org.lamport.tla.toolbox.tool.prover.ui";

    // The shared instance
    private static ProverUIActivator plugin;

    /**
     * The constructor
     */
    public ProverUIActivator()
    {
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
     */
    public void start(BundleContext context) throws Exception
    {
        super.start(context);
        plugin = this;

        /*
         * Add a resource change listener that reacts to new obligation
         * markers by updating the obligations view.
         */
        IWorkspace workspace = ResourcesPlugin.getWorkspace();

        workspace.addResourceChangeListener(new IResourceChangeListener() {

            public void resourceChanged(IResourceChangeEvent event)
            {
                final IMarkerDelta[] deltas = event.findMarkerDeltas(ProverHelper.OBLIGATION_MARKER, false);
                if (deltas.length == 0)
                {
                    return;
                }

                /*
                 * Update the obligation view with any obligation markers
                 * that have been added or modified.
                 * 
                 * If an obligation marker has been deleted, hide the obligations
                 * view. This has the effect of removing any information from the view,
                 * so that on opening, it will be re-populated with information from existing
                 * markers.
                 * 
                 * Currently, deleting a marker only occurs when the prover is launched. All
                 * markers in the currently opened spec are deleted, so this code hides
                 * and clears the obligation view to be ready for the new output from
                 * the prover.
                 */
                for (int i = 0; i < deltas.length; i++)
                {
                    if (deltas[i].getType().equals(ProverHelper.OBLIGATION_MARKER))
                    {
                        if (deltas[i].getKind() == IResourceDelta.ADDED
                                || deltas[i].getKind() == IResourceDelta.CHANGED)
                        {
                            final IMarker marker = deltas[i].getMarker();
                            UIHelper.runUIAsync(new Runnable() {

                                public void run()
                                {
                                    ObligationsView.updateObligationView(marker);
                                }
                            });

                        } else
                        {
                            UIHelper.hideView(ObligationsView.VIEW_ID);
                        }
                    }
                }

            }
        }, IResourceChangeEvent.POST_CHANGE);
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
     */
    public void stop(BundleContext context) throws Exception
    {
        plugin = null;
        super.stop(context);
    }

    /**
     * Returns the shared instance
     *
     * @return the shared instance
     */
    public static ProverUIActivator getDefault()
    {
        return plugin;
    }

    public static void logError(String string, Throwable e)
    {
        getDefault().getLog().log(new Status(IStatus.ERROR, PLUGIN_ID, string, e));
    }

    public static void logDebug(String message)
    {
        System.out.println(message);

    }

}
