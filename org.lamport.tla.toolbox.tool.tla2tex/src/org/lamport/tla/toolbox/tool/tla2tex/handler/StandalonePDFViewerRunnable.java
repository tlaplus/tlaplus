// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox.tool.tla2tex.handler;

import org.eclipse.core.resources.IResource;
import org.eclipse.ui.IWorkbenchPartSite;
import org.lamport.tla.toolbox.tool.tla2tex.view.PDFBrowser;
import org.lamport.tla.toolbox.util.UIHelper;

public class StandalonePDFViewerRunnable extends AbstractPDFViewerRunnable {

	public StandalonePDFViewerRunnable(ProducePDFHandler handler, IWorkbenchPartSite site, IResource aSpecFile) {
		super(handler, site, aSpecFile);
	}

	public void run() {
        monitor.subTask("Opening PDF File");
        
        // Can't use OS specific outputFileName as secondy id. On Windows, it 
        // contains illegal characters. Thus, use the portableString which 
        // fully identifies a module in a spec and only consists out of legal
        // chars.
        final String secondary = this.specFile.getFullPath().toPortableString();
		part = (PDFBrowser) UIHelper.openViewNoFocus(PDFBrowser.ID, secondary);
		((PDFBrowser) part).setInput(this.specFile.getName(), outputFileName);

        monitor.worked(1);
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tla2tex.handler.AbstractPDFViewerRunnable#preUpdate()
	 */
	protected void preUpdate() {
		((PDFBrowser) part).setBlank();
	}
}
