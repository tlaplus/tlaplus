package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelNameValidator;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Renames a model
 * @author Simon Zambrovski
 * @version $Id$
 */
public class RenameModelHandlerDelegate extends AbstractHandler implements IHandler, IModelConfigurationConstants
{
    private final Object RETURN = null;
    private String modelName;

    /**
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        /*
         * No parameter try to get it from active navigator if any
         */
        ISelection selection = HandlerUtil.getCurrentSelectionChecked(event);
        if (selection != null && selection instanceof IStructuredSelection)
        {
            // root file
            IResource specRootModule = ToolboxHandle.getRootModule();
            // model file
            ILaunchConfiguration model = (ILaunchConfiguration) ((IStructuredSelection) selection).getFirstElement();
            modelName = ModelHelper.getModelName(model.getFile()) + "_Copy";

            try
            {
                if (ModelHelper.isModelLocked(model))
                {
                    MessageDialog.openError(UIHelper.getShellProvider().getShell(), "Could not rename models",
                            "Could not rename the model " + modelName + ", because it is being model checked.");
                    return RETURN;
                }
            } catch (CoreException e1)
            {
                e1.printStackTrace();
            }

            IInputValidator modelNameInputValidator = new ModelNameValidator(specRootModule.getProject());
            final InputDialog dialog = new InputDialog(UIHelper.getShellProvider().getShell(), "Rename model...",
                    "Please input the new name of the model", modelName, modelNameInputValidator);
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
                // exit processing if no specName at place
                return RETURN;
            }

            final IEditorPart editor = ModelHelper.getEditorWithModelOpened(model);
            boolean wasOpened = (editor != null);
            if (wasOpened)
            {
                UIHelper.runUISync(new Runnable() {

                    public void run()
                    {
                        // close editor
                        UIHelper.getActivePage().closeEditor(editor, true);
                    }
                });
            }

            // construct real name
            String newModelName = specRootModule.getProject().getName() + "___" + modelName;
            System.out.println("Rename '" + model.getName() + "' to '" + newModelName + "'");
            try
            {
                // create the model with the new name
                ILaunchConfigurationWorkingCopy copy = model.copy(newModelName);
                copy.setAttribute(MODEL_NAME, modelName);
                copy.doSave();

                // delete the old model
                model.delete();
            } catch (CoreException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }

            // reopen
            if (wasOpened)
            {
                HashMap parameters = new HashMap();
                parameters.put(OpenModelHandler.PARAM_MODEL_NAME, modelName);
                UIHelper.runCommand(OpenModelHandler.COMMAND_ID, parameters);
            }
        }

        return RETURN;
    }

}
