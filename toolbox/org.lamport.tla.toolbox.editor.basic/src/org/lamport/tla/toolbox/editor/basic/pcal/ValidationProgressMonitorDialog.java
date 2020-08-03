/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.editor.basic.pcal;

import org.eclipse.jface.dialogs.ForkedProgressMonitorDialog;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.operation.IRunnableContext;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Shell;

import pcal.ValidationCallBack;

public class ValidationProgressMonitorDialog extends ForkedProgressMonitorDialog implements IRunnableContext, ValidationCallBack {

	private final Object lock = new Object();

	private final Listener listener = new Listener() {
		public void handleEvent(final Event e) {
			// Nothing to do here except releasing the latch.
			synchronized (lock) {
				lock.notifyAll(); // Technically, notify would suffice.
			};
		}
	};
	
	private Button continueButton;

	public ValidationProgressMonitorDialog(final Shell parent) {
		super(parent);
	}
	
	@Override
	protected void configureShell(final Shell shell) {
		super.configureShell(shell);
		// Set the title (dialog frame).
		shell.setText("Translate PlusCal Algorithm.");
	}
	
	@Override
	protected void createButtonsForButtonBar(final Composite parent) {
		// Create a second button with which the user can chose to continue.
		continueButton = createButton(parent, IDialogConstants.OK_ID, "&Overwrite Translation", true);
		continueButton.setEnabled(false); // disabled by default unless doIt explicitly called.
		continueButton.addListener(SWT.Selection, listener);
		
		// Let superclass create the cancel button to which we attach our listener.
		super.createButtonsForButtonBar(parent);
		cancel.addListener(SWT.Selection, listener);
		
		getShell().setDefaultButton(continueButton);
	}
	
	@Override
	public boolean shouldCancel() {
		// Set the label on the dialog and enable the cancel and
		// continue buttons.
		getShell().getDisplay().syncExec(() -> {
			getProgressMonitor().subTask(
					"A hash mismatch has been found that indicates that the TLA+ translation has been modified manually since its last translation.  Click the \"Overwrite Translation\" button to replace the TLA+ translation anyway or \"Cancel\" to abort re-translation and keep the modified TLA+ translation.");
			continueButton.setEnabled(true);
			cancel.setEnabled(true);
		});
		
		// Block this thread until the user presses either the cancel or continue button.
		try {
			synchronized (lock) {
				lock.wait();
			};
		} catch (InterruptedException e) {
			Thread.currentThread().interrupt();
			return true;
		}
		
		// True if the user pressed cancel button, false if continue.
		return getProgressMonitor().isCanceled();
	}
}
