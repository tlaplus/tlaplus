package org.lamport.tla.toolbox;

import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.ISpecManager;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.ui.contribution.ParseStatusContributionItem;
import org.lamport.tla.toolbox.ui.perspective.ProblemsPerspective;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;
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
    private static ISpecManager specManager;
    private ParseStatusContributionItem parseStatusWidget = null;

    /**
     * The constructor
     */
    public Activator()
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

        // register the listeners
        IWorkspace workspace = ResourcesPlugin.getWorkspace();

        // install the parse status widget
        // update widget on resource modifications
        workspace.addResourceChangeListener(new IResourceChangeListener() {

            public void resourceChanged(IResourceChangeEvent event)
            {
                UIHelper.runUIAsync(new Runnable() {

                    public void run()
                    {
                        if (parseStatusWidget == null)
                        {
                            parseStatusWidget = UIHelper.installStatusBarContributionItem();
                        }
                        parseStatusWidget.updateStatus();
                    }
                });
            }
        }, IResourceChangeEvent.POST_BUILD);

        // react with window pop-up, if set up in the preferences
        workspace.addResourceChangeListener(new IResourceChangeListener() {

            /* (non-Javadoc)
             * @see org.eclipse.core.resources.IResourceChangeListener#resourceChanged(org.eclipse.core.resources.IResourceChangeEvent)
             */
            public void resourceChanged(IResourceChangeEvent event)
            {

                UIHelper.runUIAsync(new Runnable() {
                    public void run()
                    {
                        // look up the preference for raising windows on errors
                        boolean showErrors = PreferenceStoreHelper.getInstancePreferenceStore().getBoolean(
                                IPreferenceConstants.P_PARSER_POPUP_ERRORS);
                        if (showErrors)
                        {
                            Spec spec = Activator.getSpecManager().getSpecLoaded();
                            UIHelper.closeWindow(ProblemsPerspective.ID);
                            // there were problems -> open the problem view
                            if (AdapterFactory.isProblemStatus(spec.getStatus()))
                            {
                                UIHelper.openPerspectiveInWindowRight(ProblemsPerspective.ID, null,
                                        ProblemsPerspective.WIDTH);
                            }
                        }

                    }
                });

            }

        }, IResourceChangeEvent.POST_BUILD);

    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
     */
    public void stop(BundleContext context) throws Exception
    {
        // unregister the listeners

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
    public static synchronized ISpecManager getSpecManager()
    {
        if (specManager == null)
        {
            specManager = new WorkspaceSpecManager(); // DummySpecManager();
        }
        return specManager;
    }

}
