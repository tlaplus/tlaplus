// Copyright (c) Jan 25, 2012 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
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
        if (activeEditor.isDirty())
        {
			final Shell shell = HandlerUtil.getActiveShell(event);
			final MessageDialog dialog = new SaveMessageDialog(shell, getDialogTitle(), getDialogMessage());
			if (dialog.open() == MessageDialog.CONFIRM) {
				// TODO decouple from ui thread
				activeEditor.doSave(new NullProgressMonitor());
			} else {
				return false;
			}

			// Use NullProgressMonitor instead of newly created monitor. The
			// parent ProgressMonitorDialog would need to be properly
			// initialized first.
        	// @see https://bugzilla.tlaplus.net/show_activity.cgi?id=256
        	//
			// Generally though, saving a resource involves I/O which should be
			// decoupled from the UI thread in the first place. Properly doing
			// this, would be from inside a Job which provides a ProgressMonitor
            activeEditor.doSave(new NullProgressMonitor());
        }
		return true;
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

		public SaveMessageDialog(Shell parentShell, String dialogTitle,
				String dialogMessage) {
			super(parentShell, dialogTitle, null, dialogMessage, QUESTION,
					new String[] { "Save", "Cancel" }, 0);
		}
	}
}
