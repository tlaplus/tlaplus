package org.lamport.tla.toolbox.doc.handler;

import java.net.MalformedURLException;
import java.net.URL;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;

public class HelpURLHandler extends AbstractHandler implements IHandler {

	public Object execute(final ExecutionEvent event) throws ExecutionException {
		try {
			final URL url = new URL(event.getParameter("org.lamport.tla.toolbox.doc.url.name"));
			PlatformUI.getWorkbench().getBrowserSupport().getExternalBrowser().openURL(url);
		} catch (final MalformedURLException e) {
			e.printStackTrace();
		} catch (final PartInitException e) {
			e.printStackTrace();
		}
		return null;
	}
}
