/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.operation.IRunnableContext;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.ui.handler.SaveDirtyEditorAbstractHandler;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

import pcal.Translator;

public abstract class PCalTranslator extends SaveDirtyEditorAbstractHandler {
	
	protected void translate(final TLAEditor tlaEditor, final Shell shell) throws InvocationTargetException, InterruptedException {
		translate(tlaEditor, shell, true);	
	}
	
	protected void translate(final TLAEditor tlaEditor, final Shell shell, final boolean saveEditor) throws InvocationTargetException, InterruptedException {
		// Running the PlusCal translator takes too long for the UI thread. Thus, the
		// call to the PlusCal translator call is forked off into a non-UI thread.
		// However, we use a ProgressMonitorDialog to lock the UI from further
		// modifications.
		final IRunnableContext context = new ProgressMonitorDialog(tlaEditor.getEditorSite().getShell());
		context.run(true, false, new IRunnableWithProgress() {
			public void run(final IProgressMonitor progressMonitor) throws InvocationTargetException, InterruptedException {
				final IEditorInput editorInput = tlaEditor.getEditorInput();
				final IDocument doc = tlaEditor.getDocumentProvider().getDocument(editorInput);
				final IFile file = ((FileEditorInput) editorInput).getFile();

				final Spec spec = ToolboxHandle.getCurrentSpec();

				// Remove all old markers that indicated parser problems in the previous version
				// of the editor.
				TLAMarkerHelper.removeProblemMarkers(file, progressMonitor,
						TLAMarkerHelper.TOOLBOX_MARKERS_TRANSLATOR_MARKER_ID);

				// Get the user-defined, per spec translator arguments. In almost all cases this
				// is "-nocfg".
				final List<String> asList = new ArrayList<String>(
						Arrays.asList(PreferenceStoreHelper.getStringArray(spec,
								IPreferenceConstants.PCAL_CAL_PARAMS, new String[] { "-nocfg" })));
				// Add the name of the current file to the arguments. The Translator expects
				// this even though we invoke the translator in a way that it doesn't write files.
				asList.add(file.getLocation().toOSString());

				// Run the Translator on the input and check if it succeeded. If it didn't
				// succeed, we know there are parser problems which we will use to marker the
				// editor.
				final Translator translator = new Translator(doc.get(), asList);
				if (translator.translate()) {
					// Update the mapping to/from TLA+ to PlusCal.
					spec.setTpMapping(translator.getMapping(), file.getName(), progressMonitor);

					// User might have edited a non-PlusCal part of the editor. In this case, don't
					// change the editor to not create a superfluous undo operation.
					if (translator.hasChanged()) { 
						// Join the UI thread to modify the editor's content.
						UIHelper.runUISync(new Runnable() {
							public void run() {
								// Replace the documents content while preserving the current caret position.
								final ISelection selection = tlaEditor.getViewer().getSelection();
								doc.set(translator.getOutput());
								tlaEditor.getViewer().setSelection(selection);
	
								// Finally save the editor.
								if (tlaEditor.isDirty() && saveEditor) {
									tlaEditor.doSave(progressMonitor);
								}
							}
						});
					}
				} else {
					// Add parser problem markers to the editor.
					for (Translator.Error anError : translator.getErrors()) {
						TLAMarkerHelper.installProblemMarker(file, file.getName(), IMarker.SEVERITY_ERROR,
								anError.getLocation(), anError.toString(), progressMonitor,
								TLAMarkerHelper.TOOLBOX_MARKERS_TRANSLATOR_MARKER_ID);
					}
				}
			}
		});
	}
}
