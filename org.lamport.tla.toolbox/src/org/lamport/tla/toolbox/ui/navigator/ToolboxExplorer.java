package org.lamport.tla.toolbox.ui.navigator;

import java.util.HashMap;

import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.navigator.CommonNavigator;
import org.eclipse.ui.navigator.CommonViewer;
import org.eclipse.ui.navigator.INavigatorContentService;
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
        UIHelper.runCommand(ToolboxExplorer.COMMAND_ID, new HashMap());
    }

    /**
     * Finds the CommonNavigatorViewer by name
     * @param navigatorViewId
     * @return
     */
    public static CommonNavigator findCommonNavigator(String navigatorViewId)
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
    public static CommonViewer getViewer()
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
    public static void refresh()
    {
        CommonViewer instance = getViewer();
        if (instance != null)
        {
            instance.refresh();
        }
    }

    /**
     * Sets the status of a NCE of the current viwer if any
     */
    public static void setToolboxNCEActive(final String extensionId, final boolean active)
    {
        CommonNavigator instance = findCommonNavigator(ToolboxExplorer.VIEW_ID);
        if (instance != null) 
        {
            INavigatorContentService contentService = instance.getNavigatorContentService();
            boolean isActive = contentService.getActivationService().isNavigatorExtensionActive(extensionId);
            if (active && !isActive)
            {
                contentService.getActivationService().activateExtensions(new String[] { extensionId }, false);
            } else if (!active && isActive)
            {
                contentService.getActivationService().deactivateExtensions(new String[] { extensionId }, false);
            } else
            {
                // do nothing, just quit
                return;
            }
            contentService.getActivationService().persistExtensionActivations();
            contentService.update();
        }
    }

}
