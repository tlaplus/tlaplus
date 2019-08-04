package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.lang.reflect.InvocationTargetException;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.expressions.IEvaluationContext;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.operation.IRunnableContext;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.actions.WorkspaceModifyOperation;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.util.ModelNameValidator;
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
            final Model model = (Model) ((IStructuredSelection) selection).getFirstElement();

            // a) fail if model is in use
			if (model.isRunning()) {
				MessageDialog.openError(UIHelper.getShellProvider().getShell(), "Could not rename models",
						"Could not rename the model " + model.getName()
								+ ", because it is being model checked.");
				return null;
			}
			if (model.isSnapshot()) {
				MessageDialog.openError(UIHelper.getShellProvider().getShell(), "Could not rename model",
						"Could not rename the model " + model.getName()
								+ ", because it is a snapshot.");
				return null;
			}

            // b) open dialog prompting for new model name
            final IInputValidator modelNameInputValidator = new ModelNameValidator(model.getSpec());
            final InputDialog dialog = new InputDialog(UIHelper.getShell(), "Rename model...",
                    "Please input the new name of the model", model.getName(), modelNameInputValidator);
            dialog.setBlockOnOpen(true);
            if(dialog.open() == Window.OK) {
            	// c1) close model editor if open
                IEditorPart editor = model.getAdapter(ModelEditor.class);
                if(editor != null) {
                	reopenModelEditorAfterRename = true;
                	UIHelper.getActivePage().closeEditor(editor, true);
                }
                // c2) close snapshot model editors 
                final Collection<Model> snapshots = model.getSnapshots();
				for (Model snapshot : snapshots) {
					editor = snapshot.getAdapter(ModelEditor.class);
					if (editor != null) {
						UIHelper.getActivePage().closeEditor(editor, true);
					}
				}
                
				final WorkspaceModifyOperation operation = new WorkspaceModifyOperation() {
					@Override
					protected void execute(IProgressMonitor monitor)
							throws CoreException, InvocationTargetException, InterruptedException {
						// d) rename
						final String newModelName = dialog.getValue();
						model.rename(newModelName, monitor);

						// e) reopen (in UI thread)
						if (reopenModelEditorAfterRename) {
							UIHelper.runUIAsync(new Runnable() {
								/*
								 * (non-Javadoc)
								 * 
								 * @see java.lang.Runnable#run()
								 */
								public void run() {
									Map<String, String> parameters = new HashMap<String, String>();
									parameters.put(OpenModelHandler.PARAM_MODEL_NAME, newModelName);
									UIHelper.runCommand(OpenModelHandler.COMMAND_ID, parameters);
								}
							});
						}
					}
				};
				final IRunnableContext ctxt = new ProgressMonitorDialog(UIHelper.getShell());
				try {
					ctxt.run(true, false, operation);
				} catch (InvocationTargetException | InterruptedException e) {
					throw new ExecutionException(e.getMessage(), e);
				}
             }
        }
        return null;
    }
    
    @SuppressWarnings("unchecked")	// generics casting...
	@Override
	public void setEnabled(final Object evaluationContext) {
		final Object selection = ((IEvaluationContext)evaluationContext).getDefaultVariable();
		
		if (selection instanceof List) {
			final List<Object> list = (List<Object>)selection;

			boolean modelEncountered = false; // Will always go to true on given current XML definitions; future proofing
			for (final Object element : list) {
				if (element instanceof Model) {
					if (((Model)element).isSnapshot()) {
						setBaseEnabled(false);
						
						return;
					}
					
					modelEncountered = true;
				}
			}
			
			setBaseEnabled(modelEncountered);
		} else {
			setBaseEnabled(false);
		}
	}
}