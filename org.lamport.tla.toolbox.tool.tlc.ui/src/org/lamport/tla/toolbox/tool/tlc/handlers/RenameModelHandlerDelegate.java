package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.ILaunchConfiguration;
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
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Renames a model
 */
public class RenameModelHandlerDelegate extends AbstractHandler implements IHandler, IModelConfigurationConstants
{
	/**
	 * Instructs the logic to reopen the model editor 
	 */
	private boolean reopenModelEditorAfterRename = false;

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        final ISelection selection = HandlerUtil.getCurrentSelectionChecked(event);
        if (selection != null && selection instanceof IStructuredSelection)
        {
            // model file
            final ILaunchConfiguration model = (ILaunchConfiguration) ((IStructuredSelection) selection).getFirstElement();

            // root file
            final IResource specRootModule = ToolboxHandle.getRootModule(model.getFile().getProject());

            // a) fail if model is in use or locked
            final String modelName = ModelHelper.getModelName(model.getFile()) + "_Copy";
			try {
				if (ModelHelper.isModelRunning(model) || ModelHelper.isModelLocked(model)) {
					MessageDialog.openError(UIHelper.getShellProvider().getShell(), "Could not rename models",
							"Could not rename the model " + modelName
									+ ", because it is being model checked or is locked.");
					return null;
				}
			} catch (CoreException e1) {
				throw new ExecutionException(e1.getMessage(), e1);
			}

            // b) open dialog prompting for new model name
            final IInputValidator modelNameInputValidator = new ModelNameValidator(specRootModule.getProject());
            final InputDialog dialog = new InputDialog(UIHelper.getShell(), "Rename model...",
                    "Please input the new name of the model", modelName, modelNameInputValidator);
            dialog.setBlockOnOpen(true);
            if(dialog.open() == Window.OK) {
            	// c) close model editor if open
                final IEditorPart editor = ModelHelper.getEditorWithModelOpened(model);
                if(editor != null) {
                	reopenModelEditorAfterRename = true;
                	UIHelper.getActivePage().closeEditor(editor, true);
                }
                
                final Job j = new ToolboxJob("Renaming model...") {
					/* (non-Javadoc)
					 * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
					 */
					protected IStatus run(IProgressMonitor monitor) {
						// d) rename
						final String newModelName = dialog.getValue();
						ModelHelper.renameModel(model, ModelHelper.getSpecPrefix(model), newModelName);

						// e) reopen (in UI thread)
			            if (reopenModelEditorAfterRename) {
				            UIHelper.runUIAsync(new Runnable(){
								/* (non-Javadoc)
								 * @see java.lang.Runnable#run()
								 */
								public void run() {
									Map<String, String> parameters = new HashMap<String, String>();
									parameters.put(OpenModelHandler.PARAM_MODEL_NAME, newModelName);
									UIHelper.runCommand(OpenModelHandler.COMMAND_ID, parameters);
								}
				            });
			            }
						return Status.OK_STATUS;
					}
				};
				j.schedule();
            }
        }
        return null;
    }
}
