package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;
import java.util.List;
import java.util.Vector;

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
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelNameValidator;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;

/**
 * Handler for creation of new models
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class NewModelHandler extends AbstractHandler implements IModelConfigurationConstants
{
    public static final String COMMAND_ID = "toolbox.tool.tlc.commands.model.new";
    public static final String PARAM_SPEC_NAME = "toolbox.tool.tlc.commands.model.new.param";
    // public static final String PARAM_SPEC_NAME = "specName";

    private String modelName = null;

    /**
     * The constructor.
     */
    public NewModelHandler()
    {
    }

    /**
     *  This method is called when the TLC Model Checker / New Model command 
     *  is executed.  The last thing it does is call the Eclipse magic that
     *  calls the appropriate methods to open the model pages.  Thus, any
     *  initial settings of values in the model is done here by setting
     *  the appropriate attributes of the model.
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        String parameter = event.getParameter(PARAM_SPEC_NAME);
        Spec spec = null;
        if (parameter != null)
        {
            spec = ToolboxHandle.getSpecByName(parameter);
        } else
        {
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
                "Please input the name of the model to create", modelName, modelNameInputValidator);

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
            ILaunchConfigurationWorkingCopy launchCopy = launchConfigurationType.newInstance(specProject, specProject
                    .getName()
                    + "___" + modelName);

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

            // Initialize the Specification field of the model to be the
            // temporal formula Spec if Spec is defined by the current
            // specification to be a temporal formula. Otherwise, initialize
            // that field to be a specification with initial predicate field
            // Init and next-state action Next if those names are defined to
            // be operators of the appropriate level.
            //
            // Also, if Spec is found and Termination is defined to be a
            // temporal formula, then add it to the list of temporal properties,
            // except not checked.  It should be checked iff the root file 
            // contains a PlusCal spec and the -termination option has been
            // selected, either as a property or in the file.
            OpDefNode[] defs = moduleNode.getOpDefs();
            boolean foundSpec = false;
            boolean foundInit = false;
            boolean foundNext = false;
            boolean foundTermination = false;
            for (int i = 0; i < defs.length; i++)
            {
                if (defs[i].getName().toString().equals("Spec") && (defs[i].getLevel() == LevelNode.TemporalLevel))
                {
                    foundSpec = true;

                } else if (defs[i].getName().toString().equals("Init")
                        && (defs[i].getLevel() == LevelNode.VariableLevel))
                {
                    foundInit = true;
                } else if (defs[i].getName().toString().equals("Next") && (defs[i].getLevel() == LevelNode.ActionLevel))
                {
                    foundNext = true;

                } else if (defs[i].getName().toString().equals("Termination")
                        && (defs[i].getLevel() == LevelNode.TemporalLevel))
                {
                    foundTermination = true;

                }
            }
            if (foundSpec)
            {
                launchCopy.setAttribute(IModelConfigurationConstants.MODEL_BEHAVIOR_CLOSED_SPECIFICATION, "Spec");
                launchCopy.setAttribute(IModelConfigurationConstants.MODEL_BEHAVIOR_SPEC_TYPE,
                        IModelConfigurationDefaults.MODEL_BEHAVIOR_TYPE_SPEC_CLOSED);
                if (foundTermination)
                {
                    Vector vec = new Vector();
                    launchCopy.setAttribute(MODEL_PROPERTIES_EXPAND, "set");
                    vec.add("0Termination");
                    // The first character should be 1 or 0 depending
                    // on whether or not the box enabling the property should be checked.
                    launchCopy.setAttribute(IModelConfigurationConstants.MODEL_CORRECTNESS_PROPERTIES, vec);
                }
            } else if (foundInit && foundNext) {
                launchCopy.setAttribute(IModelConfigurationConstants.MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, "Init");
                launchCopy.setAttribute(IModelConfigurationConstants.MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, "Next");
                launchCopy.setAttribute(IModelConfigurationConstants.MODEL_BEHAVIOR_SPEC_TYPE,
                        IModelConfigurationDefaults.MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT);
            }
            // Set a test initial property to check.

            ILaunchConfiguration launchSaved = launchCopy.doSave();

            // create parameters for the handler
            HashMap parameters = new HashMap();
            parameters.put(OpenModelHandler.PARAM_MODEL_NAME, modelName);

            // runs the command and opens the module [should be model?] in the editor
            //
            // Attempted explanation by LL:
            // It appears that through some multiple levels of Eclipse-induced
            // indirection, this causes the ModelEditor.openPages() method to
            // be called, which is what actually creates the model pages and
            // puts them on the screen. See the commands for UIHelper.runCommand.
            //
            UIHelper.runCommand(OpenModelHandler.COMMAND_ID, parameters);

            return launchSaved;

        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error creating a model", e);
        }

        return null;
    }

}
