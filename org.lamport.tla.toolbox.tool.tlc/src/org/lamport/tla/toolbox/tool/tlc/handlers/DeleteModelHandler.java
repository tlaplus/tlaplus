package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Deletes the launch configuration
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DeleteModelHandler extends AbstractHandler implements IModelConfigurationConstants
{
    public static final String PARAM_MODEL_NAME = "toolbox.tool.tlc.commands.model.delete.param";
    public static final String COMMAND_ID = "toolbox.tool.tlc.commands.model.delete";

    /**
     * The constructor.
     */
    public DeleteModelHandler()
    {
    }

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // get the launch manager
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();

        // get the launch type (model check)
        ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_ID);

        String modelName = event.getParameter(DeleteModelHandler.PARAM_MODEL_NAME);
        if (modelName == null)
        {
            System.out.println("Leaving delte model handler. No model name specified.");
            return null;
        }
        System.out.println("Delete model '" + modelName + "'");
        
        try
        {
            ILaunchConfiguration[] launchConfigurations = launchManager
                    .getLaunchConfigurations(launchConfigurationType);
            for (int i = 0; i < launchConfigurations.length; i++)
            {
                // skip launches from other specs (projects)
                if (modelName.equals(ModelHelper.getModelName(launchConfigurations[i].getFile())))
                {
                    launchConfigurations[i].delete();
                }
            }
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }

}
