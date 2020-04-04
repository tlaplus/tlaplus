// Copyright (c) Jan 25, 2012 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * @author Markus Alexander Kuppe
 */
public abstract class SaveDirtyEditorAbstractHandler extends AbstractHandler {

	protected IEditorPart activeEditor;

	/**
	 * @param event
	 * @return true iff the dirty editor has been saved, false otherwise
	 */
	public boolean saveDirtyEditor(final ExecutionEvent event) {
		activeEditor = UIHelper.getActiveEditor();
		if (activeEditor.isDirty()) {
			getPrefs().setDefault(this.getClass() + ".dontBother", false);
			if (getPrefs().getBoolean(this.getClass() + ".dontBother")) {
				// TODO decouple from ui thread
				// Use NullProgressMonitor instead of newly created monitor. The
				// parent ProgressMonitorDialog would need to be properly
				// initialized first.
				// @see Bug #256 in general/bugzilla/index.html
				//
				// Generally though, saving a resource involves I/O which should be
				// decoupled from the UI thread in the first place. Properly doing
				// this, would be from inside a Job which provides a ProgressMonitor
				activeEditor.doSave(new NullProgressMonitor());
			} else {
				final Shell shell = HandlerUtil.getActiveShell(event);
				final MessageDialog dialog = new SaveMessageDialog(shell, getDialogTitle(), getDialogMessage());
				int res = dialog.open();
				if (res == 2) { // 2 is index of button in string[] below
					// User doesn't want to be warned about a dirty editor any longer.
					// Remember it for this handler (this.getClass).
					getPrefs().setValue(this.getClass() + ".dontBother", true);
					res = MessageDialog.OK;
				}
				if (res == MessageDialog.OK || res == MessageDialog.CONFIRM) {
					// TODO decouple from ui thread
					// Use NullProgressMonitor instead of newly created monitor. The
					// parent ProgressMonitorDialog would need to be properly
					// initialized first.
					// @see Bug #256 in general/bugzilla/index.html
					//
					// Generally though, saving a resource involves I/O which should be
					// decoupled from the UI thread in the first place. Properly doing
					// this, would be from inside a Job which provides a ProgressMonitor
					activeEditor.doSave(new NullProgressMonitor());
				} else {
					return false;
				}
			}
		}
		return true;
	}

	private IPreferenceStore getPrefs() {
		return Activator.getDefault().getPreferenceStore();
	}

	protected String getDialogMessage() {
		return "The current editor has not been saved, should the editor be saved first?";
	}

	protected String getDialogTitle() {
		return "Save " + activeEditor.getTitle() + " editor?";
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		if (UIHelper.getActiveEditor() == null) {
			return false;
		}
		return super.isEnabled();
	}

	/**
	 * A {@link MessageDialog#QUESTION} style dialog with special save/cancel buttons
	 */
	private class SaveMessageDialog extends MessageDialog {

		public SaveMessageDialog(Shell parentShell, String dialogTitle, String dialogMessage) {
			super(parentShell, dialogTitle, null, dialogMessage, QUESTION,
					new String[] { "&Save", "&Cancel", "Save and &never ask again" }, 0);
		}
	}
}
