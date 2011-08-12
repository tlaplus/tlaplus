package org.lamport.tla.toolbox.tool.prover.ui;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.lamport.tla.toolbox.tool.prover.ui.output.data.ColorPredicate;
import org.lamport.tla.toolbox.tool.prover.ui.preference.ProverPreferencePage;
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

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
     */
    public void start(BundleContext context) throws Exception
    {
        super.start(context);
        plugin = this;

        UIHelper.runUIAsync(new Runnable() {
			
			public void run() {
		        IPreferenceStore store = EditorsUI.getPreferenceStore();

		        /*
		         * The following sets the default color predicates for the colors. First argument
		         * is the key for each predicate for the logical color, and the second argument is
		         * the predicate string (not the macro name).
		         */
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(1), ColorPredicate.PREDICATE_NONE);
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(2), ColorPredicate.PREDICATE_NONE);
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(3), ColorPredicate.PREDICATE_BEING_PROVED);
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(4), ColorPredicate.PREDICATE_STOPPED);
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(5), ColorPredicate.PREDICATE_FAILED);
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(6), ColorPredicate.PREDICATE_PROVED);
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(7), ColorPredicate.PREDICATE_PROVED_OR_OMITTED);
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(8), ColorPredicate.PREDICATE_PROVED_OR_OMITTED_OR_MISSING);
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(9), ColorPredicate.PREDICATE_NONE);
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(10), ColorPredicate.PREDICATE_NONE);
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(11), ColorPredicate.PREDICATE_NONE);
		        store.setDefault(ProverPreferencePage.getColorPredPrefName(12), ColorPredicate.PREDICATE_NONE);

		        store.setDefault(ProverPreferencePage.getLeafSideBarPrefName(3), true);
		        store.setDefault(ProverPreferencePage.getLeafSideBarPrefName(4), true);
		        store.setDefault(ProverPreferencePage.getLeafSideBarPrefName(5), true);
			}
		});
         /*
         * DR commented out the following because default colors are now set in the plugin.xml file for this
         * plug-in.
         */
        //
        // /*
        // * The following sets the default colors values.
        // */
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(1), new RGB(255, 187, 187));
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(2), new RGB(255, 255, 183));
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(3), new RGB(217, 250, 174));
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(4), new RGB(133, 133, 133));
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(5), new RGB(174, 255, 174));
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(6), new RGB(0, 0, 0));
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(7), new RGB(0, 0, 0));
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(8), new RGB(0, 0, 0));
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(9), new RGB(0, 0, 0));
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(10), new RGB(0, 0, 0));
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(11), new RGB(0, 0, 0));
        // PreferenceConverter.setDefault(store, ProverPreferencePage.getColorPrefName(12), new RGB(0, 0, 0));

        /*
         * The following was commented out by DR to make it easier to
         * understand how the obligations view is updated. Initially this
         * code got new obligation markers indirectly through a resource
         * change listener and passed them to the obligation view. Now
         * the obligations view is informed of new markers and of marker
         * deletions by the classes that call the marker creation and deletion,
         * namely, TagBasedTLAPMOutputIncrementalParser and ProverJob.
         * Add a resource change listener that reacts to new obligation
         * markers by updating the obligations view.
         */
        // IWorkspace workspace = ResourcesPlugin.getWorkspace();
        //
        // workspace.addResourceChangeListener(new IResourceChangeListener() {
        //
        // public void resourceChanged(IResourceChangeEvent event)
        // {
        // final IMarkerDelta[] deltas = event.findMarkerDeltas(ProverHelper.OBLIGATION_MARKER, false);
        // if (deltas.length == 0)
        // {
        // return;
        // }
        //
        // /*
        // * Update the obligation view with any obligation markers
        // * that have been added or modified.
        // *
        // * If any obligation markers have been deleted, this indicates that the prover
        // * has been relaunched. When the prover is relaunched, old obligation
        // * markers are deleted. We can clear the information of these old obligation
        // * markers from the obligation view by calling
        // * ObligationView.refreshObligationView().
        // */
        // boolean markersDeleted = false;
        // for (int i = 0; i < deltas.length; i++)
        // {
        // if (deltas[i].getType().equals(ProverHelper.OBLIGATION_MARKER))
        // {
        // if (deltas[i].getKind() == IResourceDelta.ADDED
        // || deltas[i].getKind() == IResourceDelta.CHANGED)
        // {
        // final IMarker marker = deltas[i].getMarker();
        // UIHelper.runUIAsync(new Runnable() {
        //
        // public void run()
        // {
        // ObligationsView.updateObligationView(marker);
        // }
        // });
        //
        // } else
        // {
        // markersDeleted = true;
        // }
        // }
        // }
        //
        // if (markersDeleted)
        // {
        // UIHelper.runUIAsync(new Runnable() {
        //
        // public void run()
        // {
        // ObligationsView.refreshObligationView();
        // }
        // });
        // }
        //
        // }
        // }, IResourceChangeEvent.POST_CHANGE);

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

    public static void logError(String message, Throwable e)
    {
        getDefault().getLog().log(new Status(IStatus.ERROR, PLUGIN_ID, message, e));
    }

    public static void logDebug(String message)
    {
    	//getDefault().getLog().log(new Status(IStatus.INFO, PLUGIN_ID, message));

    	// why oh why use the log FW when you can dump everything to the console
    	// and let the user figure out what is important and what not
        System.out.println(message);
    }
}
