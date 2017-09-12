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
package org.lamport.tla.toolbox.ui.view;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

public class PDFBrowserEditor extends EditorPart {

	public static final String ID = "org.lamport.tla.toolbox.PDFBrowserEditor";
	
	private Browser browser;

	@Override
	public void init(IEditorSite site, IEditorInput input) throws PartInitException {
		setSite(site);
		setInput(input);
		this.setPartName(input.getName());
		if (browser != null && input instanceof IFileEditorInput) {
			setFileInput((IFileEditorInput) input);
		}
	}

	@Override
	public void createPartControl(Composite parent) {
		final Composite body = new Composite(parent, SWT.NONE);
        body.setLayout(new FillLayout());
        this.browser = new Browser(body, SWT.NONE);
        if (getEditorInput() instanceof IFileEditorInput) {
        	setFileInput((IFileEditorInput) getEditorInput());
        } else {
        	this.browser.setText("<html><body></body></html>");
        }
	}

	private void setFileInput(IFileEditorInput input) {
		this.browser.setUrl(input.getFile().getLocationURI().toASCIIString());
	}

	@Override
	public void setFocus() {
		this.browser.getParent().setFocus();
	}
	
	//** Methods below not relevant because PDF editor is read-only. **//
	
	@Override
	public boolean isDirty() {
		return false;
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
		// unsupported
	}

	@Override
	public void doSaveAs() {
		// unsupported
	}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}
}
