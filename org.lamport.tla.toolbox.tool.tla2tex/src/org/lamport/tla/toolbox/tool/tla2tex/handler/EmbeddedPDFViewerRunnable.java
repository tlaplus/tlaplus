// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox.tool.tla2tex.handler;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.PartInitException;
import org.lamport.tla.toolbox.util.UIHelper;

public class EmbeddedPDFViewerRunnable extends AbstractPDFViewerRunnable {

	public EmbeddedPDFViewerRunnable(final ProducePDFHandler handler, final IWorkbenchPartSite site, final IResource aSpecFile) {
		super(handler, site, aSpecFile);
	}

	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		monitor.subTask("Opening PDF File");

		try {
			//TODO Open on part stack next to the spec editor
			part = UIHelper.openEditorUnchecked(
					// Referencing de.vonloesch...
					// creates an _implicit_
					// dependency which is not made
					// explicit in the bundle's
					// Manifest
					"de.vonloesch.pdf4eclipse.editors.PDFEditor",
					outputFile,
					false); // don't activate (give focus) the editor
		} catch (PartInitException e) {
			MessageDialog.openWarning(UIHelper.getShellProvider().getShell(),
					"PDF File Not Modified",
					"The pdf file could not be modified. "
							+ "Make sure that the file " + outputFileName
							+ " is not open in any external programs.");
		}
		
		monitor.worked(1);
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tla2tex.handler.AbstractPDFViewerRunnable#setFile(java.lang.String)
	 */
	@Override
	public void setFile(String outputFileName) throws CoreException {
		super.setFile(outputFileName);
		// explicitly touch the file to trigger a resource change event that is
		// received by the pdf editor. This causes the pdf editor to refresh its
		// content, if it has been open with the same pdf file already
		this.outputFile.touch(new NullProgressMonitor());
	}
}
