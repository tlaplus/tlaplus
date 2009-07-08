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
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.window.Window;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelNameValidator;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.ModuleNode;

/**
 * Handler for creation of new models
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class NewModelHandler extends AbstractHandler implements IModelConfigurationConstants
{
    private String modelName = null;

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
        modelName = ModelHelper.constructModelName(specRootModule.getProject());

        IInputValidator modelNameInputValidator = new ModelNameValidator(specRootModule.getProject());
        final InputDialog dialog = new InputDialog(UIHelper.getShellProvider().getShell(), "New model...",
                "Plese input the name of the model to create", modelName, modelNameInputValidator);

        dialog.setBlockOnOpen(true);
        UIHelper.runUISync(new Runnable() {

            public void run()
            {
                int open = dialog.open();
                switch (open) {
                case Window.OK:
                    modelName = dialog.getValue();
                    break;
                case Window.CANCEL:
                    // cancel model creation
                    modelName = null;
                }
            }
        });
        if (modelName == null)
        {
            // exit processing if no model name at place
            return null;
        }
        
        if (ToolboxHandle.getSpecObj() == null) 
        {
            // TODO
            System.out.println("BUG: no specObject");
            return null;
        }
        
        // get the root module
        ModuleNode moduleNode = ToolboxHandle.getSpecObj().getExternalModuleTable().getRootModule();

        // get the list of constants
        List constants = ModelHelper.createConstantsList(moduleNode);

        try
        {

            // create new launch instance
            ILaunchConfigurationWorkingCopy launchCopy = launchConfigurationType.newInstance(specRootModule
                    .getProject(), specRootModule.getProject().getName() + "___" + modelName);

            launchCopy.setAttribute(SPEC_NAME, ToolboxHandle.getCurrentSpec().getName());
            launchCopy.setAttribute(SPEC_ROOT_FILE, specRootModule.getLocation().toOSString());
            // FIXME change the model name on rename!
            launchCopy.setAttribute(MODEL_NAME, modelName);
            
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
