package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.ui.navigator.CommonNavigator;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;

public class ModelExplorer extends CommonNavigator
{
    public static String VIEW_ID = "toolbox.tool.tlc.ModelView";

    /**
     * Return the initial input for the model explorer (the Launch config Type)
     */
    protected IAdaptable getInitialInput()
    {
        ILaunchConfigurationType launchConfigurationType = DebugPlugin.getDefault().getLaunchManager()
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_ID);
        return launchConfigurationType;
    }

}
