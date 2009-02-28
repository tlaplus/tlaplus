package org.lamport.tla.toolbox.tool.tlc.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.model.ILaunchConfigurationDelegate;
import org.eclipse.debug.core.model.LaunchConfigurationDelegate;

/**
 * Represents a launch delegate for TLC
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCModelLaunchDelegate extends LaunchConfigurationDelegate implements ILaunchConfigurationDelegate
{
    public static final String LAUNCH_ID = "org.lamport.tla.toolbox.tool.tlc.modelCheck";
    
    
    public void launch(ILaunchConfiguration configuration, String mode, ILaunch launch, IProgressMonitor monitor)
            throws CoreException
    {
        System.out.println("Started in mode : " + mode);
        
    }

}
