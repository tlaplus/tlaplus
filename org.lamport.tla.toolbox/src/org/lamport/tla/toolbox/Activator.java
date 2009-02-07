package org.lamport.tla.toolbox;

import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.ISpecManager;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.spec.parser.ParserDependencyStorage;
import org.lamport.tla.toolbox.ui.contribution.ParseStatusContributionItem;
import org.lamport.tla.toolbox.ui.perspective.ProblemsPerspective;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
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
    private static ParserDependencyStorage parserDependencyStorage;
    private ParseStatusContributionItem parseStatusWidget = null;

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

        // install the parse status widget
        UIHelper.runUIAsync(new Runnable() {

            public void run()
            {
                parseStatusWidget = UIHelper.getStatusBarContributionItem();
                parseStatusWidget.updateStatus();
            }
        });
        
        
        // update widget on resource modifications
        workspace.addResourceChangeListener(new IResourceChangeListener() {

            public void resourceChanged(IResourceChangeEvent event)
            {
                UIHelper.runUIAsync(new Runnable() {

                    public void run()
                    {
                        parseStatusWidget = UIHelper.getStatusBarContributionItem();
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
            public void resourceChanged(final IResourceChangeEvent event)
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
                            
                            // Instead of explicit status check, look on the problem markers  
                            // if (AdapterFactory.isProblemStatus(spec.getStatus()))
                            if (TLAMarkerHelper.getProblemMarkers(spec.getProject(), null).length > 0)
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
    public static synchronized ISpecManager getSpecManager()
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

}
