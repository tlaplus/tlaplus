// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox.tool.tla2tex.handler;

import java.io.File;

import org.eclipse.jface.dialogs.MessageDialog;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.util.UIHelper;


public class StandalonePDFViewerRunnable extends AbstractPDFViewerRunnable {

	private final TLAEditorAndPDFViewer tlaEditorAndPDFViewer;

	public StandalonePDFViewerRunnable(
			TLAEditorAndPDFViewer tlaEditorAndPDFViewer) {
				this.tlaEditorAndPDFViewer = tlaEditorAndPDFViewer;
	}

	public void run() {
        monitor.subTask("Opening PDF File");
        tlaEditorAndPDFViewer.setActivePage(TLAEditorAndPDFViewer.PDFPage_ID);
        tlaEditorAndPDFViewer.getPDFViewingPage().getBrowser().setUrl(outputFileName);
        monitor.worked(1);

        if (new File(outputFileName).lastModified() < translationStartTime)
        {
            MessageDialog.openWarning(UIHelper.getShellProvider().getShell(),
                    "PDF File Not Modified", "The pdf file could not be modified. "
                            + "Make sure that the file " + outputFileName
                            + " is not open in any external programs.");
        }
	}
}
