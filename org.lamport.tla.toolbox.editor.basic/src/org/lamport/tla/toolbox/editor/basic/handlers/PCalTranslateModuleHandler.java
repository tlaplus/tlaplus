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
 *   Simon Zambrowski - initial API and implementation
 *   Markus Alexander Kuppe - Refactoring
 ******************************************************************************/
package org.lamport.tla.toolbox.editor.basic.handlers;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.editor.basic.pcal.PCalTranslator;
import org.lamport.tla.toolbox.ui.handler.SaveDirtyEditorAbstractHandler;

/**
 * Triggers the PCal translation of the module
 * 
 * @author Simon Zambrovski
 */
public class PCalTranslateModuleHandler extends SaveDirtyEditorAbstractHandler {

	public Object execute(final ExecutionEvent event) throws ExecutionException {
		if (!saveDirtyEditor(event)) {
			// Cannot translate a dirty editor.
			return null;
		}
		final TLAEditor tlaEditor = getTLAEditor(activeEditor);
		if (tlaEditor == null || !tlaEditor.hasPlusCal()) {
			// If it's not a TLAEditor, it can't have PlusCal code.
			return null;
		}

		try {
			new PCalTranslator().translate(tlaEditor, HandlerUtil.getActiveShell(event));
		} catch (InvocationTargetException | InterruptedException e) {
			throw new ExecutionException(e.getMessage(), e);
		}
		return null;
	}
	
	private static TLAEditor getTLAEditor(IEditorPart anEditor) {
		if (anEditor instanceof TLAEditorAndPDFViewer) {
			final TLAEditorAndPDFViewer editor = (TLAEditorAndPDFViewer) anEditor;
			return editor.getTLAEditor();
		}
		if (anEditor instanceof TLAEditor) {
			return (TLAEditor) anEditor;
		}
		return null;
	}
}
