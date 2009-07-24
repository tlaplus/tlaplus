package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Clones the launch configuration
 */
public class CloneModelHandler extends AbstractHandler implements IModelConfigurationConstants
{
    public static final String PARAM_MODEL_NAME = "toolbox.tool.tlc.commands.model.open.param.modelName";
    public static final String PARAM_MODELCOPY_NAME = "toolbox.tool.tlc.commands.model.open.param.modelCloneName";
    public static final String COMMAND_ID = "toolbox.tool.tlc.commands.model.clone";

    /**
     * The constructor.
     */
    public CloneModelHandler()
    {
    }

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // get the launch manager
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();

        // get the launch type (model check)
        ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);

        String modelName = event.getParameter(PARAM_MODEL_NAME);
        String modelCopyName = event.getParameter(PARAM_MODELCOPY_NAME);
        if (modelName == null)
        {
            return null;
        }

        try
        {
            ILaunchConfiguration[] launchConfigurations = launchManager
                    .getLaunchConfigurations(launchConfigurationType);
            for (int i = 0; i < launchConfigurations.length; i++)
            {
                // skip launches from other specs (projects)
                if (modelName.equals(launchConfigurations[i].getName()))
                {
                    ILaunchConfigurationWorkingCopy copy = launchConfigurations[i].copy(modelCopyName);
                    copy.setAttribute(MODEL_NAME, ModelHelper.getModelName(copy.getFile()));
                    copy.doSave();
                    break;
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
