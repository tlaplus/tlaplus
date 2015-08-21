package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.Iterator;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;

public class DeleteModelHandler extends AbstractHandler implements IHandler
{

    /**
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    @SuppressWarnings("unchecked")
	public Object execute(ExecutionEvent event) throws ExecutionException
    {
		// Get the currently selected models from the Eclipse SelectionService
		// (Ask UI what the current selection is). The CommandFramework makes
		// sure that only ILaunchConfigurations can be part of the selection.
        final ISelection selection = HandlerUtil.getCurrentSelectionChecked(event);
        if (selection != null && selection instanceof IStructuredSelection) {
        	final IStructuredSelection iss = (IStructuredSelection) selection;

        	// 1.) get confirmation from the user to delete all files/models
        	// if user cancels, just return
        	int amountOfModels = iss.size();
			boolean userConfirmedDeletion = MessageDialog.openQuestion(
					UIHelper.getShell(), "Confirm Delete",
					"Are you sure you want to delete " + amountOfModels
							+ " model(s)?");
			if(!userConfirmedDeletion) {
				return null;
			}
				 
			// 2.) user has confirmed deletion
			// check if any of the models is
			// currently running a model check
			// TODO better disable delete action in spec explorer for
			// currently model checking models
			final Iterator<ILaunchConfiguration> itr1 = iss.iterator();
			for (; itr1.hasNext();) {
        		final ILaunchConfiguration ilc = itr1.next();
        		try {
					boolean modelIsRunning = ModelHelper.isModelRunning(ilc);
					if(modelIsRunning) {
						MessageDialog
								.openError(
										UIHelper.getShell(),
										"Could not delete a model",
										"Could not delete the model "
												+ ModelHelper.getModelName(ilc.getFile())
												+ ", because it is being model checked.");
						return null;
					}
				} catch (CoreException e) {
					// Can't think of a situation where this would throw a CoreException
					// (except for an impl bug in isModelRunning()) at this point.
					e.printStackTrace();
				}
			}
			
			// 3.) at this point, we are safe to delete all models (user has
			// confirmed, no model is used in model checking
			// But there might be open editors corresponding to the models which have to be closed first
			final Iterator<ILaunchConfiguration> itr2 = iss.iterator();
			for (; itr2.hasNext();) {
        		final ILaunchConfiguration ilc = itr2.next();

        		// close corresponding editor if open
				final IEditorPart editorWithModelOpened = ModelHelper
						.getEditorWithModelOpened(ilc);
				if (editorWithModelOpened != null) {
					UIHelper.getActivePage().closeEditor(editorWithModelOpened,
							false);
				}
			}
			
			// Remove all to be deleted LaunchConfigs from the Selection so that
			// other UI handlers do not handle them during the backend job
			
			// Simply convert selection to ILC[]
			final ILaunchConfiguration[] ilcs = (ILaunchConfiguration[]) iss
			.toList().toArray(new ILaunchConfiguration[iss.size()]);

			// 3.) remove any tlc output sources corresponding to this model
			// in case the user opens a new model of the same name in
			// the same toolbox session
			TLCOutputSourceRegistry.getModelCheckSourceRegistry()
					.removeTLCStatusSource(ilcs);
			
			// 4.) UI is in ready state
			// Defer deletion to ResourceFramework outside the UI thread (makes
			// it cancel-able too, keeps track of conflicting resource
			// modifications, ...)
			final Job job = new ToolboxJob("Deleting models...") {
				@Override
				protected IStatus run(IProgressMonitor monitor) {
					try {
						ModelHelper.deleteModels(ilcs, monitor);
					} catch (CoreException e) {
						return new Status(Status.ERROR,
								"org.lamport.tla.toolbox.tool.tlc.ui",
								e.getMessage(), e);
					}
					return Status.OK_STATUS;
				}
			};
			job.schedule();
        }
        return null;
    }
}
