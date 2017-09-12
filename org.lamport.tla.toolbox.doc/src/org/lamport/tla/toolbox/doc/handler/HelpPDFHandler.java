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
import org.eclipse.ui.PartInitException;
import org.lamport.tla.toolbox.doc.HelpActivator;
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.framework.Bundle;

public class HelpPDFHandler extends AbstractHandler implements IHandler {

	public Object execute(ExecutionEvent event) throws ExecutionException {
		final String pdf = event.getParameter("org.lamport.tla.toolbox.doc.pdf.file");
		final String name = event.getParameter("org.lamport.tla.toolbox.doc.pdf.name");
		try {
			UIHelper.openEditorUnchecked(
					// Referencing de.vonloesch...
					// creates an _implicit_
					// dependency which is not made
					// explicit in the bundle's
					// Manifest
					"de.vonloesch.pdf4eclipse.editors.PDFEditor", getDocFile("/pdfs/" + pdf), name, false);
		} catch (PartInitException e) {
			HelpActivator.getDefault().logError(e.getMessage(), e);
		} catch (IOException e) {
			HelpActivator.getDefault().logError(e.getMessage(), e);
		} catch (URISyntaxException e) {
			HelpActivator.getDefault().logError(e.getMessage(), e);
		}
		return null;
	}

	private File getDocFile(final String bundleRelativePath) throws IOException, URISyntaxException {
		final Bundle bundle = Platform.getBundle(HelpActivator.PLUGIN_ID);
		return new File(FileLocator.resolve(bundle.getEntry(bundleRelativePath)).toURI());
	}
}
