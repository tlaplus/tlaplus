package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;
import java.util.List;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.ModuleNode;

/**
 * Our sample handler extends AbstractHandler, an IHandler base class.
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class NewModelHandler extends AbstractHandler implements IModelConfigurationConstants
{
    public static final Object PARAM_MODEL_NAME = "modelLaunchName";

    /**
     * The constructor.
     */
    public NewModelHandler()
    {
    }

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // root file
        IResource specRootModule = ToolboxHandle.getRootModule();

        // root module name
        String rootModuleName = ResourceHelper.getModuleName(specRootModule);

        // get the launch manager
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();

        // get the launch type (model check)
        ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_ID);

        // retrieve a new model name for the spec
        String modelName = ModelHelper.constructModelName(specRootModule.getProject(), ToolboxHandle.getCurrentSpec()
                .getName());

        // get the model root file
        IResource modelRoot = ModelHelper.getNewModelRootFile(specRootModule, modelName);

        // get the model configuration
        IResource config = ModelHelper.getConfigFile(modelRoot);

        // get the root module
        ModuleNode moduleNode = ToolboxHandle.getSpecObj().getExternalModuleTable().getRootModule();

        // get the list of constants
        List constants = ModelHelper.createConstantsList(moduleNode);

        try
        {

            // create new launch instance
            ILaunchConfigurationWorkingCopy launchCopy = launchConfigurationType.newInstance(specRootModule
                    .getProject(), modelName);

            launchCopy.setAttribute(SPEC_NAME, ToolboxHandle.getCurrentSpec().getName());
            launchCopy.setAttribute(SPEC_ROOT_FILE, ToolboxHandle.getRootModule().getLocation().toOSString());
            launchCopy.setAttribute(SPEC_ROOT_MODULE, rootModuleName);
            launchCopy.setAttribute(MODEL_NAME, modelName);
            launchCopy.setAttribute(MODEL_ROOT_FILE, modelRoot.getLocation().toOSString());
            launchCopy.setAttribute(CONFIG_FILE, config.getLocation().toOSString());
            if (constants.size() == 0)
            {
                launchCopy.setAttribute(MODEL_PARAMETER_CONSTANTS, (List) null);
            } else
            {
                launchCopy.setAttribute(MODEL_PARAMETER_CONSTANTS, ModelHelper.serializeAssignmentList(constants));
            }

            ILaunchConfiguration launchSaved = launchCopy.doSave();

            
            // create parameters for the handler
            HashMap parameters = new HashMap();
            parameters.put(OpenModelHandler.PARAM_MODEL_NAME, modelName);

            // runs the command and opens the module in the editor
            UIHelper.runCommand(OpenModelHandler.COMMAND_ID, parameters);
            
            return launchSaved;

        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        
        
        
        return null;
    }

}
