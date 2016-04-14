// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox.tool.tla2tex.handler;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.e4.core.services.events.IEventBroker;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IPartService;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartSite;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.osgi.service.event.Event;
import org.osgi.service.event.EventHandler;

public abstract class AbstractPDFViewerRunnable  implements EventHandler, IPartListener, Runnable {

	protected IFile outputFile;
	protected IProgressMonitor monitor;
	protected String outputFileName;
	
	private final ProducePDFHandler handler;
	protected final IResource specFile;
	protected IWorkbenchPart part;
	
	public AbstractPDFViewerRunnable(ProducePDFHandler handler, IWorkbenchPartSite site, IResource aSpecFile) {
		Assert.isNotNull(handler);
		Assert.isNotNull(site);
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

	public void setFile(String outputFileName) throws CoreException {
        this.outputFileName = outputFileName;
		this.outputFile = (IFile) ResourceHelper.getResourceByName(outputFileName);
	}

	public void setMonitor(IProgressMonitor monitor) {
		this.monitor = monitor;
	}

	protected void preUpdate() {
		// No-op
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
				preUpdate();
				handler.runPDFJob(this, specFile);
			}
		}
	}
	
	/* IPartListener */

	/* (non-Javadoc)
	 * @see org.eclipse.ui.IPartListener#partClosed(org.eclipse.ui.IWorkbenchPart)
	 */
	public void partClosed(IWorkbenchPart aPart) {
		// Listen for PDFEditor close events to de-register this event listener
		// from receiving further TLAEditor/save events. If the user closes the
		// PDFEditor, it implicitly means she's no longer interested in the PDF.
		if (aPart == part) {
			final IEventBroker service = aPart.getSite().getService(IEventBroker.class);
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
