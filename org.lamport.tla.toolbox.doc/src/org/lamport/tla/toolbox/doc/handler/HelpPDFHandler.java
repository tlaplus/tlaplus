/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
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
package org.lamport.tla.toolbox.doc.handler;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Platform;
import org.eclipse.swt.custom.BusyIndicator;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.PartInitException;
import org.lamport.tla.toolbox.doc.HelpActivator;
import org.lamport.tla.toolbox.ui.view.PDFBrowser;
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.framework.Bundle;

public class HelpPDFHandler extends AbstractHandler implements IHandler {

	public Object execute(ExecutionEvent event) throws ExecutionException {
		final String pdf = event.getParameter("org.lamport.tla.toolbox.doc.pdf.file");
		final String name = event.getParameter("org.lamport.tla.toolbox.doc.pdf.name");
		
		// For historical reasons this preference is found in the tlatex bundle. Thus,
		// we read the value from there, but don't refer to the corresponding string
		// constants to not introduce a plugin dependency.
		// org.lamport.tla.toolbox.tool.tla2tex.TLA2TeXActivator.PLUGIN_ID
		// org.lamport.tla.toolbox.tool.tla2tex.preference.ITLA2TeXPreferenceConstants.EMBEDDED_VIEWER
		final boolean useEmbeddedViewer = Platform.getPreferencesService()
				.getBoolean("org.lamport.tla.toolbox.tool.tla2tex", "embeddedViewer", false, null);
		
		// Show a sandglass while loading (large) pdfs.
		BusyIndicator.showWhile(Display.getCurrent(), new Runnable() {
			public void run() {
				try {
					final File pdfFile = getDocFile("/pdfs/" + pdf);
					if (useEmbeddedViewer) {
						UIHelper.openEditorUnchecked(
								// Referencing de.vonloesch...
								// creates an _implicit_
								// dependency which is not made
								// explicit in the bundle's
								// Manifest
								"de.vonloesch.pdf4eclipse.editors.PDFEditor", pdfFile, name, false);
					} else {
						final IViewPart view = UIHelper.openViewNoFocus(PDFBrowser.ID, name);
						((PDFBrowser) view).setInput(name, pdfFile.toURI().toURL().toString());
					}
				} catch (PartInitException e) {
					HelpActivator.getDefault().logError(e.getMessage(), e);
				} catch (IOException e) {
					HelpActivator.getDefault().logError(e.getMessage(), e);
				} catch (URISyntaxException e) {
					HelpActivator.getDefault().logError(e.getMessage(), e);
				}
			}
		});
		return null;
	}

	private File getDocFile(final String bundleRelativePath) throws IOException, URISyntaxException {
		final Bundle bundle = Platform.getBundle(HelpActivator.PLUGIN_ID);
		return new File(FileLocator.resolve(bundle.getEntry(bundleRelativePath)).toURI());
	}
}
