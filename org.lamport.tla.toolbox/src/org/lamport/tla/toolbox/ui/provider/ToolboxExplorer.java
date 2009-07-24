package org.lamport.tla.toolbox.ui.provider;

import java.util.HashMap;

import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.ui.IPerspectiveListener;
import org.eclipse.ui.navigator.CommonNavigator;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandlerDelegate;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Specification Explorer
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ToolboxExplorer extends CommonNavigator
{
    public final static String VIEW_ID = "toolbox.view.ToolboxExplorer";

    /**
     * Override the method to deliver the root object for the NCE activation
     */
    protected Object getInitialInput()
    {
        return Activator.getSpecManager();
    }

    /**
     * Open a model on double-click
     */
    protected void handleDoubleClick(DoubleClickEvent anEvent)
    {
        super.handleDoubleClick(anEvent);
        // open the model
        UIHelper.runCommand(OpenSpecHandlerDelegate.COMMAND_ID, new HashMap());
        
        IPerspectiveListener l;
    }

    
    
}
