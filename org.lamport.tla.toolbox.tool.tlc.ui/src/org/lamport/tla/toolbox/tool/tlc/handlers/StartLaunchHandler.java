package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

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

			final ILaunchConfiguration config = modelEditor.getConfig().getOriginal();

			// 0) model check already running for the given model
			try {
				if (ModelHelper.isModelRunning(config)) {
					return null;
				}
			} catch (CoreException e1) {
				// why oh why does isModelRunning throw an exception?!
				return null;
			}

			// 1) if editor is dirty, ask if we should save
			final Shell shell = HandlerUtil.getActiveShell(event);
			if (modelEditor.isDirty()) {
				boolean save = MessageDialog.openQuestion(shell, "Save model?",
						"The current model has not been saved, should the model be saved prior to launching?");
				if (save) {
					// TODO decouple from ui thread
					modelEditor.doSaveWithoutValidating(new NullProgressMonitor());
				} else {
					return null;
				}
			}

			// 2) model might be locked
			if (modelEditor.isModelLocked()) {
				boolean unlock = MessageDialog
						.openQuestion(shell, "Unlock model?",
								"The current model is locked, but has to be unlocked prior to launching. Should the model be unlocked?");
				if (unlock) {
					try {
						ModelHelper.setModelLocked(config, false);
					} catch (CoreException e) {
						throw new ExecutionException(e.getMessage(), e);
					}
				} else {
					return null;
				}
			}

			// 3) model might be stale
			if (modelEditor.isModelStale()) {
				boolean unlock = MessageDialog
						.openQuestion(shell, "Repair model?",
								"The current model is stale and has to be repaird prior to launching. Should the model be repaired onw?");
				if (unlock) {
					try {
						ModelHelper.recoverModel(config);
					} catch (CoreException e) {
						throw new ExecutionException(e.getMessage(), e);
					}
				} else {
					return null;
				}
			}

			// finally launch (for some reason config.launch(..) does not work %)
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
		return lastModelEditor;
	}
}
