package org.lamport.tla.toolbox.tool.tlc.launch.ui;

import org.eclipse.debug.ui.AbstractLaunchConfigurationTabGroup;
import org.eclipse.debug.ui.ILaunchConfigurationDialog;
import org.eclipse.debug.ui.ILaunchConfigurationTab;

public class ModelCheckerTabGroup extends AbstractLaunchConfigurationTabGroup
{

    public ModelCheckerTabGroup()
    {
    }

    /**
     * Constructs the tabs to be included in the launch configuration
     */
    public void createTabs(ILaunchConfigurationDialog dialog, String mode)
    {
        ILaunchConfigurationTab[] tabs = new ILaunchConfigurationTab[] { new ModelConfigurationTab(), };
        setTabs(tabs);
    }

}
