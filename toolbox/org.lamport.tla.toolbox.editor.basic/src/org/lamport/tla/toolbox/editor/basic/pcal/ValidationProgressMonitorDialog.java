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

import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;

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
	
	private Button continueButton;

	private Button thirdButton;

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
		thirdButton = createButton(parent, IDialogConstants.OK_ID, "&Overwrite Translation", true);
		thirdButton.setEnabled(false); // disabled by default unless doIt explicitly called.
		thirdButton.setVisible(false);
		
		// Create a second button with which the user can chose to continue.
		continueButton = createButton(parent, IDialogConstants.OK_ID, "&Overwrite Translation", true);
		continueButton.setEnabled(false); // disabled by default unless doIt explicitly called.
		
		// Let superclass create the cancel button to which we attach our listener.
		super.createButtonsForButtonBar(parent);
		cancel.setText("&Abort");
		
		getShell().setDefaultButton(continueButton);
	}
	
	@Override
	public boolean shouldCancel() {

		final Object lock = new Object();

		final Listener listener = new Listener() {
			public void handleEvent(final Event e) {
				// Nothing to do here except releasing the latch.
				synchronized (lock) {
					lock.notifyAll(); // Technically, notify would suffice.
				};
			}
		};

		// Set the label on the dialog and enable the cancel and
		// continue buttons.
		getShell().getDisplay().syncExec(() -> {
			getProgressMonitor().setTaskName("Overwrite modified TLA+ translation?");
			getProgressMonitor().subTask(
					"The TLA+ translation has been manually modified since its last translation (chksum(tla) mismatch).  Click the \"Overwrite Translation\" button to replace the TLA+ translation anyway or \"Cancel\" to abort re-translation and keep the modified TLA+ translation.");
			continueButton.setText("&Overwrite Translation");
			continueButton.setEnabled(true);
			continueButton.addListener(SWT.Selection, listener);
			cancel.setText("&Abort");
			cancel.setEnabled(true);
			cancel.addListener(SWT.Selection, listener);
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
	
	@Override
	public Generate shouldGenerate() {
		final BlockingQueue<Generate> q = new ArrayBlockingQueue<>(1);
		
		// Set the label on the dialog and enable the cancel and
		// continue buttons.
		getShell().getDisplay().syncExec(() -> {
			getProgressMonitor().setTaskName("Add Checksums to TLA+ translation?");
			getProgressMonitor().subTask(
					"The PlusCal translator can add checksums to the \\* BEGIN TRANSLATION line of this spec to warn you before model-checking a stale TLA+ translation. Do you want to add checksums, never add checksums, or decide later?");
			continueButton.setText("&Add Checksums");
			continueButton.setEnabled(true);
			continueButton.addListener(SWT.Selection,(e) -> q.offer(Generate.DO_IT));
			cancel.setText("&Later");
			cancel.setEnabled(true);
			cancel.addListener(SWT.Selection,(e) -> q.offer(Generate.NOT_NOW));
			thirdButton.setText("&Never Add");
			thirdButton.setEnabled(true);
			thirdButton.setVisible(true);
			thirdButton.addListener(SWT.Selection,(e) -> q.offer(Generate.IGNORE));
		});
		
		try {
			return q.take();
		} catch (InterruptedException e) {
			Thread.currentThread().interrupt();
			return Generate.NOT_NOW;
		}
	}
}
