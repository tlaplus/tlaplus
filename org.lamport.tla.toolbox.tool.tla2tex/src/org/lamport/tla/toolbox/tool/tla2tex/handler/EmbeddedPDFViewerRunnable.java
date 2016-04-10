// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox.tool.tla2tex.handler;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.e4.core.services.events.IEventBroker;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IPartService;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;
import org.eclipse.ui.PartInitException;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.service.event.Event;
import org.osgi.service.event.EventHandler;

public class EmbeddedPDFViewerRunnable extends AbstractPDFViewerRunnable implements EventHandler, IPartListener {

	private IEditorPart pdfEditor;
	private final ProducePDFHandler handler;
	private final IResource specFile;
	
	public EmbeddedPDFViewerRunnable(final ProducePDFHandler handler, final IWorkbenchPartSite site, final IResource aSpecFile) {
		Assert.isNotNull(handler);
		Assert.isNotNull(aSpecFile);
		this.handler = handler;
		this.specFile = aSpecFile;
		
		// Subscribe to the event bus with which the TLA Editor save events are
		// distributed. In other words, every time the user saves a spec, we
		// receive an event and provided the spec corresponds to this PDF, we
		// regenerate it.
		// Don't subscribe in EmbeddedPDFViewerRunnable#though, because it is run
		// repeatedly and thus would cause us to subscribe multiple times.
		final IEventBroker eventService = site.getService(IEventBroker.class);
		Assert.isTrue(eventService.subscribe(TLAEditor.SAVE_EVENT, this));
		
		// Register for part close events to deregister the event handler
		// subscribed to the event bus. There is no point in regenerating
		// the PDF if no PDFEditor is open anymore.
		final IPartService partService = site.getService(IPartService.class);
		partService.addPartListener(this);
	}

	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		monitor.subTask("Opening PDF File");

		try {
			//TODO Open on part stack next to the spec editor
			pdfEditor = UIHelper.openEditorUnchecked(
					// Referencing de.vonloesch...
					// creates an _implicit_
					// dependency which is not made
					// explicit in the bundle's
					// Manifest
					"de.vonloesch.pdf4eclipse.editors.PDFEditor",
					outputFile);
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

	/* EventHandler */
	
	/* (non-Javadoc)
	 * @see org.osgi.service.event.EventHandler#handleEvent(org.osgi.service.event.Event)
	 */
	public void handleEvent(final Event event) {
		// Listen for TLAEditor/save to regenerate the PDF and refresh the
		// editor iff the event DATA corresponds to this.specFile. There might
		// be several PDFs open each responsible for a certain spec.
		if (TLAEditor.SAVE_EVENT.equals(event.getTopic())) {
			final Object property = event.getProperty(IEventBroker.DATA);
			if (property instanceof IFile && this.specFile.equals(property)) {
				handler.runPDFJob(this, specFile);
			}
		}
	}
	
	/* IPartListener */

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IPartListener#partClosed(org.eclipse.ui.IWorkbenchPart)
	 */
	public void partClosed(IWorkbenchPart part) {
		// Listen for PDFEditor close events to de-register this event listener
		// from receiving further TLAEditor/save events. If the user closes the
		// PDFEditor, it implicitly means she's no longer interested in the PDF.
		if (part == pdfEditor) {
			final IEventBroker service = part.getSite().getService(IEventBroker.class);
			service.unsubscribe(this);
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IPartListener#partActivated(org.eclipse.ui.IWorkbenchPart)
	 */
	public void partActivated(IWorkbenchPart part) {
		// no-op
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IPartListener#partBroughtToTop(org.eclipse.ui.IWorkbenchPart)
	 */
	public void partBroughtToTop(IWorkbenchPart part) {
		// no-op
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IPartListener#partDeactivated(org.eclipse.ui.IWorkbenchPart)
	 */
	public void partDeactivated(IWorkbenchPart part) {
		// no-op
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IPartListener#partOpened(org.eclipse.ui.IWorkbenchPart)
	 */
	public void partOpened(IWorkbenchPart part) {
		// no-op
	}
}
