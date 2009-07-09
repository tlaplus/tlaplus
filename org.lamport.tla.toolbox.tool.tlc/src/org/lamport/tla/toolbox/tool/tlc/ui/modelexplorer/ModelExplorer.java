package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

import java.util.HashMap;

import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.ui.navigator.CommonNavigator;
import org.lamport.tla.toolbox.tool.tlc.handlers.OpenModelHandlerDelegate;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Implementation of the model explorer
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelExplorer extends CommonNavigator
{
    public static String VIEW_ID = "toolbox.tool.tlc.ModelView";

    /**
     * Return the initial input for the model explorer (the Launch config Type)
     */
    protected Object getInitialInput()
    {
        ILaunchConfigurationType launchConfigurationType = DebugPlugin.getDefault().getLaunchManager()
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_ID);
        return launchConfigurationType;
    }

    /**
     * Open a model on double-click
     */
    protected void handleDoubleClick(DoubleClickEvent anEvent)
    {
        super.handleDoubleClick(anEvent);
        // open the model
        UIHelper.runCommand(OpenModelHandlerDelegate.COMMAND_ID, new HashMap());
    }
}
