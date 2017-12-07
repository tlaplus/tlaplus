package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.text.SimpleDateFormat;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;

public class DeleteModelHandler extends AbstractHandler implements IHandler
{
	private static final SimpleDateFormat sdf = new SimpleDateFormat("MMM dd,yyyy HH:mm:ss");

    /**
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    @SuppressWarnings("unchecked")
	public Object execute(ExecutionEvent event) throws ExecutionException
    {
		// Get the currently selected models from the Eclipse SelectionService
		// (Ask UI what the current selection is). The CommandFramework makes
		// sure that only Model can be part of the selection.
        final ISelection selection = HandlerUtil.getCurrentSelectionChecked(event);
        if (selection != null && selection instanceof IStructuredSelection) {
        	final IStructuredSelection iss = (IStructuredSelection) selection;

        	// 1.) get confirmation from the user to delete all files/models
        	// if user cancels, just return
			boolean userConfirmedDeletion = MessageDialog.openQuestion(
					UIHelper.getShell(), "Confirm Delete",
					getLabel(iss));
			if(!userConfirmedDeletion) {
				return null;
			}
				 
			// 2.) user has confirmed deletion
			// check if any of the models is
			// currently running a model check
			// TODO better disable delete action in spec explorer for
			// currently model checking models
			final Iterator<Model> itr1 = iss.iterator();
			for (; itr1.hasNext();) {
        		final Model model = itr1.next();
				if(model.isRunning()) {
					MessageDialog
							.openError(
									UIHelper.getShell(),
									"Could not delete a model",
									"Could not delete the model "
											+ model.getName()
											+ ", because it is being model checked.");
					return null;
				}
			}
			
			// 3.) at this point, we are safe to delete all models (user has
			// confirmed, no model is used in model checking
			// But there might be open editors corresponding to the models which have to be closed first
			final Iterator<Model> itr2 = iss.iterator();
			for (; itr2.hasNext();) {
        		final Model model = itr2.next();

        		// close corresponding editor if open
        		final IEditorPart editorWithModelOpened = model.getAdapter(ModelEditor.class);
				if (editorWithModelOpened != null) {
					UIHelper.getActivePage().closeEditor(editorWithModelOpened,
							false);
				}
			}
			
			// Remove all to be deleted Models from the Selection so that
			// other UI handlers do not handle them during the backend job
			
			// Simply convert selection to ILC[]
			final Model[] models = (Model[]) iss
			.toList().toArray(new Model[iss.size()]);

			// 3.) remove any tlc output sources corresponding to this model
			// in case the user opens a new model of the same name in
			// the same toolbox session
			TLCOutputSourceRegistry.getModelCheckSourceRegistry()
					.removeTLCStatusSource(models);
			
			// 4.) UI is in ready state
			// Defer deletion to ResourceFramework outside the UI thread (makes
			// it cancel-able too, keeps track of conflicting resource
			// modifications, ...)
			final Job job = new ToolboxJob("Deleting models...") {
				@Override
				protected IStatus run(IProgressMonitor monitor) {
					try {
						for (Model model : models) {
							model.delete(monitor);
						}
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

	private String getLabel(final IStructuredSelection iss) {
		if (iss.size() > 1) {
			// The selected models.
			@SuppressWarnings("unchecked")
			final List<Model> list = (List<Model>) iss.toList();
			final Predicate<Model> p = Model::isSnapshot;
			final Set<Model> models = list.stream().filter(p.negate()).collect(Collectors.toSet());

			if (models.isEmpty()) {
				// Only Snapshots are selected.
				return String.format("Are you sure you want to delete the %s selected snapshots?", iss.size());
			} else {
				// The set of snapshots (either explicitly selected or implicit via parent
				// model) to be deleted.
				final Set<Model> allSnapshots = list.stream().map(Model::getSnapshots).flatMap(c -> c.stream())
						.collect(Collectors.toSet());

				if (models.size() > 1 && allSnapshots.isEmpty()) {
					return String.format("Are you sure you want to delete the %s selected models?", iss.size());
				} else {
					// The set of selected snapshots to be deleted.
					final Set<Model> selectedSnapshots = list.stream().filter(Model::isSnapshot)
							.collect(Collectors.toSet());

					if (models.size() == 1) {
						// 1 Model with its snapshots and selected snapshots.
						allSnapshots.addAll(selectedSnapshots);
						return String.format("Are you sure you want to delete the select model '%s' and %s snapshot%s?",
								models.iterator().next().getName(), allSnapshots.size(),
								isPlural(allSnapshots));
					} else {
						// N models with M snapshots
						allSnapshots.addAll(selectedSnapshots);
						return String.format("Are you sure you want to delete %s models and %s snapshot%s?",
								models.size(), allSnapshots.size(), isPlural(allSnapshots));
					}
				}
			}
		}
		return getLabel((Model) iss.getFirstElement());
	}
	
	private String getLabel(Model model) {
		final Model snapshotFor = model.getSnapshotFor();
		if (snapshotFor != model) {
			return String.format("Are you sure you want to delete the snapshot of %s of model '%s'?",
					sdf.format(model.getSnapshotTimeStamp()), snapshotFor.getName());
		}
		final Collection<Model> snapshots = model.getSnapshots();
		if (!snapshots.isEmpty()) {
			return String.format("Are you sure you want to delete the model '%s' and its %s snapshot%s?", model.getName(),
					snapshots.size(), isPlural(snapshots));
		}
		return String.format("Are you sure you want to delete the model '%s'?", model.getName());
	}
	
	private static String isPlural(final Collection<?> col) {
		return col.size() > 1 ? "s" : "";
	}
}
