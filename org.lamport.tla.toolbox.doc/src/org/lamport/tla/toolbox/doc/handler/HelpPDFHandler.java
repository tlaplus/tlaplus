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
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.framework.Bundle;

public class HelpPDFHandler extends AbstractHandler implements IHandler {

	public Object execute(ExecutionEvent event) throws ExecutionException {
		final String pdf = event.getParameter("org.lamport.tla.toolbox.doc.pdf.name");
		try {
			UIHelper.openEditorUnchecked(
					// Referencing de.vonloesch...
					// creates an _implicit_
					// dependency which is not made
					// explicit in the bundle's
					// Manifest
					"de.vonloesch.pdf4eclipse.editors.PDFEditor", getDocFile("/pdfs/" + pdf), false);
		} catch (PartInitException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		} catch (URISyntaxException e) {
			e.printStackTrace();
		}
		return null;
	}

	private File getDocFile(final String bundleRelativePath) throws IOException, URISyntaxException {
		final Bundle bundle = Platform.getBundle("org.lamport.tla.toolbox.doc");
		return new File(FileLocator.resolve(bundle.getEntry(bundleRelativePath)).toURI());
	}
}
