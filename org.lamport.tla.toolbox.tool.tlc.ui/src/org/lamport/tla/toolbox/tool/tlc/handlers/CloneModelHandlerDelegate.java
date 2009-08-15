package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IResource;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelNameValidator;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Renames a model
 * @author Simon Zambrovski
 * @version $Id$
 */
public class CloneModelHandlerDelegate extends AbstractHandler implements IHandler
{

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
            // model
            ILaunchConfiguration model = (ILaunchConfiguration) ((IStructuredSelection) selection).getFirstElement();

            // root file
            IResource specRootModule = ToolboxHandle.getRootModule(model.getFile().getProject());

            
            modelName = ModelHelper.getModelName(model.getFile()) + "_Copy";

            IInputValidator modelNameInputValidator = new ModelNameValidator(specRootModule.getProject());
            final InputDialog dialog = new InputDialog(UIHelper.getShellProvider().getShell(), "Clone model...",
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
                return null;
            }

            final IEditorPart editor = ModelHelper.getEditorWithModelOpened(model);
            boolean wasOpened = (editor != null);

            // construct real name
            String newModelName = specRootModule.getProject().getName() + "___" + modelName;
            // System.out.println("Clone '" + model.getName() + "' and save under '" + newModelName + "'");

            HashMap parameters = null;

            // clone the model
            parameters = new HashMap();
            parameters.put(CloneModelHandler.PARAM_MODEL_NAME, model.getName());
            parameters.put(CloneModelHandler.PARAM_MODELCOPY_NAME, newModelName);
            UIHelper.runCommand(CloneModelHandler.COMMAND_ID, parameters);

            // original model was open
            if (wasOpened)
            {
                parameters = new HashMap();
                parameters.put(OpenModelHandler.PARAM_MODEL_NAME, modelName);
                UIHelper.runCommand(OpenModelHandler.COMMAND_ID, parameters);
            }
        }

        return null;
    }

}
