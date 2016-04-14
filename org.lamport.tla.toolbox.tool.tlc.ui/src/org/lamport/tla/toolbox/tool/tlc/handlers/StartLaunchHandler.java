package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchSite;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;

/**
 * Initiates a model checker run
 */
public class StartLaunchHandler extends AbstractHandler {

	/**
	 * The last launched model editor or null if no previous launch has happened
	 */
	private ModelEditor lastModelEditor;

	public Object execute(ExecutionEvent event) throws ExecutionException {
		final ModelEditor modelEditor = getModelEditor(event);
		if (modelEditor != null) {

			final Model model = modelEditor.getModel();

			// 0) model check already running for the given model
			if (model.isRunning()) {
				return null;
			}

			// 0.5) Ask and save _spec_ editor if it's dirty
			final Shell shell = HandlerUtil.getActiveShell(event);
			final IWorkbenchSite site = HandlerUtil.getActiveSite(event);
			final IEditorReference[] editors = site.getPage().getEditorReferences();
			for (IEditorReference ref : editors) {
				if (OpenSpecHandler.TLA_EDITOR_CURRENT.equals(ref.getId())) {
					if (ref.isDirty()) {
						final String title = ref.getName();
						boolean save = MessageDialog.openQuestion(shell, "Save " + title + " spec?", "The spec "
								+ title + " has not been saved, should the spec be saved prior to launching?");
						if (save) {
							// TODO decouple from ui thread
							ref.getEditor(true).doSave(new NullProgressMonitor());

							// Wait for the AutoBuilder to parse the spec.
							// Unless we wait here, the spec might actually in
							// the unparsed state by the time we try to launch
							// TLC. This launch will subsequently fail
							// due to the spec's unparsed state.
							try {
								Job.getJobManager().join(ResourcesPlugin.FAMILY_AUTO_BUILD, new NullProgressMonitor());
							} catch (OperationCanceledException e) {
								throw new ExecutionException(e.getMessage(), e);
							} catch (InterruptedException e) {
								throw new ExecutionException(e.getMessage(), e);
							}
						} else {
							return null;
						}
					}
				}
			}

			// 1) if model editor is dirty, save it
			if (modelEditor.isDirty()) {
				// TODO decouple from ui thread
				modelEditor.doSaveWithoutValidating(new NullProgressMonitor());
			}

			// 2) model might be locked
			if (model.isLocked()) {
				boolean unlock = MessageDialog
						.openQuestion(shell, "Unlock model?",
								"The current model is locked, but has to be unlocked prior to launching. Should the model be unlocked?");
				if (unlock) {
					model.setLocked(false);
				} else {
					return null;
				}
			}

			// 3) model might be stale
			if (model.isStale()) {
				boolean unlock = MessageDialog
						.openQuestion(shell, "Repair model?",
								"The current model is stale and has to be repaird prior to launching. Should the model be repaired onw?");
				if (unlock) {
					model.recover();
				} else {
					return null;
				}
			}

			// finally launch (for some reason config.launch(..) does not work
			// %)
			modelEditor.launchModel(TLCModelLaunchDelegate.MODE_MODELCHECK, true);
		}
		return null;
	}

	private ModelEditor getModelEditor(final ExecutionEvent event) {
		// is current editor a model editor?
		final String activeEditorId = HandlerUtil.getActiveEditorId(event);
		if (activeEditorId != null && activeEditorId.startsWith(ModelEditor.ID)) {
			lastModelEditor = (ModelEditor) HandlerUtil.getActiveEditor(event);
		}
		// If lastModelEditor is still null, it means we haven't run the model
		// checker yet AND the model editor view is *not* active. Lets search
		// through all editors to find a model checker assuming only a single one
		// is open right now. If more than one model editor is open, randomly
		// select one. In case it's not the one intended to be run by the user,
		// she has to activate the correct model editor manually.
		//
		// It is tempting to store the name of the lastModelEditor
		// in e.g. an IDialogSetting to persistently store even across Toolbox
		// restarts. However, the only way to identify a model editor here is by
		// its name and almost all model editors carry the name "Model_1" (the
		// default name). So we might end up using Model_1 which was the last
		// model that ran for spec A, but right now spec B and two of its model
		// editors are open ("Model_1" and "Model_2"). It would launch Model_1,
		// even though Model_2 might be what the user wants.
		if (lastModelEditor == null) {
			final IWorkbenchWindow workbenchWindow = HandlerUtil.getActiveWorkbenchWindow(event);
			final IWorkbenchPage[] pages = workbenchWindow.getPages();
			for (final IWorkbenchPage page : pages) {
				final IEditorReference[] editorReferences = page.getEditorReferences();
				for (final IEditorReference editorRefs: editorReferences) {
					if (editorRefs.getId().equals(ModelEditor.ID)) {
						lastModelEditor = (ModelEditor) editorRefs.getEditor(true);
						break;
					}
				}
			}
		}
		// Validate that the lastModelEditor still belongs to the current
		// open spec. E.g. lastModelEditor might still be around from when
		// the user ran a it on spec X, but has switched to spec Y in the
		// meantime. Closing the spec nulls the ModelEditor
		if (lastModelEditor.isDisposed()) {
			lastModelEditor = null;
		}
		
		// If the previous two attempts to find a model editor have failed, lets
		// return whatever we have... which might be null.
		return lastModelEditor;
	}
}
