package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.launch.ui.IConfigurationConstants;

/**
 * Opens a model configuration
 * @author Simon Zambrovski 
 * @version $Id$
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class OpenModelHandler extends AbstractHandler implements IConfigurationConstants
{
    public static final String COMMAND_ID = "org.lamport.tla.toolbox.tool.tlc.commands.modellaunch.open";
    public static final Object PARAM_MODEL_NAME = "org.lamport.tla.toolbox.tool.tlc.commands.modellaunch.open.param";


    /**
     * The constructor.
     */
    public OpenModelHandler()
    {
    }

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        String modelName = event.getParameter((String) PARAM_MODEL_NAME);
    
        System.out.println("Open handler invoked on " +  modelName);
        
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        ILaunchConfigurationType launchConfigurationType = launchManager
        .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_ID);

        try
        {
            ILaunchConfiguration[] launchConfigurations = launchManager.getLaunchConfigurations(launchConfigurationType);
            for (int i = 0; i < launchConfigurations.length; i++)
            {
                if (launchConfigurations[i].getName().equals(modelName)) 
                {
                    NewModelHandler.openLaunchDialog(launchConfigurations[i]);
                    break;
                }
            }
            
            
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        
        System.out.println("Finished open handler");
        
        return null;
    }
}
