package org.lamport.tla.toolbox.ui.navigator;

import java.util.HashMap;

import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.navigator.CommonNavigator;
import org.eclipse.ui.navigator.CommonViewer;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Specification Explorer
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ToolboxExplorer extends CommonNavigator
{
    public final static String VIEW_ID = "toolbox.view.ToolboxExplorer";
    public static final String COMMAND_ID = "toolbox.command.cnf.open.delegate";
    
	/**
     * Override the method to deliver the root object for the NCE activation
     */
    protected Object getInitialInput()
    {
        return Activator.getSpecManager();
    }

    /**
     * Open on double-click
     */
    protected void handleDoubleClick(DoubleClickEvent anEvent)
    {
        super.handleDoubleClick(anEvent);
        // open the model
        UIHelper.runCommand(ToolboxExplorer.COMMAND_ID, new HashMap<String, String>());
    }

    /**
     * Finds the CommonNavigatorViewer by name
     * @param navigatorViewId
     * @return
     */
    private static CommonNavigator findCommonNavigator(String navigatorViewId)
    {
        IWorkbenchPage page = UIHelper.getActivePage();
        if (page != null)
        {
            IViewPart findView = UIHelper.getActivePage().findView(navigatorViewId);
            if (findView != null && findView instanceof CommonNavigator)
            {
                return ((CommonNavigator) findView);
            }
        }
        return null;
    }

    /**
     * Retrieves the current viewer if any
     * @return the instance of common viewer or <code>null</code>
     */
    private static CommonViewer getViewer()
    {
        CommonNavigator navigator = findCommonNavigator(ToolboxExplorer.VIEW_ID);
        if (navigator != null) 
        {
            return navigator.getCommonViewer();
        }
        
        return null;
    } 

    /**
     * Refreshes the instance of the viewer if any
     */
    private static void refresh()
    {
        CommonViewer instance = getViewer();
        if (instance != null)
        {
            instance.refresh();
        }
    }
//
//    /**
//     * Sets the status of a NCE of the current viwer if any
//     */
//    private static void setToolboxNCEActive(final String extensionId, final boolean active)
//    {
//        CommonNavigator instance = findCommonNavigator(ToolboxExplorer.VIEW_ID);
//        if (instance != null) 
//        {
//            INavigatorContentService contentService = instance.getNavigatorContentService();
//            boolean isActive = contentService.getActivationService().isNavigatorExtensionActive(extensionId);
//            if (active && !isActive)
//            {
//                contentService.getActivationService().activateExtensions(new String[] { extensionId }, false);
//            } else if (!active && isActive)
//            {
//                contentService.getActivationService().deactivateExtensions(new String[] { extensionId }, false);
//            } else
//            {
//                // do nothing, just quit
//                return;
//            }
//            contentService.getActivationService().persistExtensionActivations();
//            contentService.update();
//        }
//    }

    /*
	 * Use an inner class because instantiation of ProblemView itself should be
	 * left to the Eclipse foundation and not be triggered directly via new.
	 */
    public static class ResourceListener implements IResourceChangeListener {

		private static ResourceListener INSTANCE;

		public synchronized static void init() {
			if (INSTANCE == null) {
				INSTANCE = new ResourceListener();
			}
		}

    	private ResourceListener() {
			// We might have missed events during Toolbox startup when there was
			// a workspace but no UI yet.
    		resourceChanged(null);
    		
            // update CNF viewers
    		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
    		workspace.addResourceChangeListener(this);
    	}
    	
		public void resourceChanged(IResourceChangeEvent event) {
			UIHelper.runUIAsync(new Runnable() {
				public void run() {
					ToolboxExplorer.refresh();
				}
			});
		}
    }
}
