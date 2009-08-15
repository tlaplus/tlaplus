package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;
import java.util.List;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.window.Window;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelNameValidator;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;

/**
 * Handler for creation of new models
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class NewModelHandler extends AbstractHandler implements IModelConfigurationConstants
{
    public static final String COMMAND_ID       = "toolbox.tool.tlc.commands.model.new";
    public static final String PARAM_SPEC_NAME  = "toolbox.tool.tlc.commands.model.new.param";
//    public static final String PARAM_SPEC_NAME  = "specName";
    
    private String modelName = null;

    /**
     * The constructor.
     */
    public NewModelHandler()
    {
    }

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        String parameter = event.getParameter(PARAM_SPEC_NAME);
        Spec spec = null;
        if (parameter != null) 
        {
            spec = ToolboxHandle.getSpecByName(parameter);
        } else {
            spec = ToolboxHandle.getCurrentSpec();
        }
        if (spec == null) 
        {
            // no spec
            System.out.println("BUG: no spec");
            return null;
        }
        // project
        IProject specProject = spec.getProject();
        
        // root module
        // IResource specRootModule = spec.getRootFile();

        // spec object
        SpecObj specObject = spec.getRootModule();
        if (specObject == null) 
        {
            System.out.println("BUG: no specObject");
            return null;
        }

        
        
        
        // get the launch manager
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();

        // get the launch type (model check)
        ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);

        // retrieve a new model name for the spec
        modelName = ModelHelper.constructModelName(specProject);

        IInputValidator modelNameInputValidator = new ModelNameValidator(specProject);
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
        
        
        // get the root module
        ModuleNode moduleNode = specObject.getExternalModuleTable().getRootModule();

        // get the list of constants
        List constants = ModelHelper.createConstantsList(moduleNode);

        try
        {

            // create new launch instance
            ILaunchConfigurationWorkingCopy launchCopy = launchConfigurationType.newInstance(specProject, specProject.getName() + "___" + modelName);

            launchCopy.setAttribute(SPEC_NAME, spec.getName());
            // it is easier to do launchCopy.getProject().getPersistentProperty(SPEC_ROOT_FILE)
            // launchCopy.setAttribute(SPEC_ROOT_FILE, specRootModule.getLocation().toOSString());
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
            TLCUIActivator.logError("Error creating a model", e);
        }

        return null;
    }

}
