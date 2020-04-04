package org.lamport.tla.toolbox.tool.tla2tex.handler;

import org.eclipse.core.resources.IResource;
import org.eclipse.ui.IWorkbenchPartSite;
import org.lamport.tla.toolbox.tool.tla2tex.TLA2TeXActivator;

public class OperatingSystemPDFRunnable extends AbstractPDFViewerRunnable {
	/** We have no need for any of these parameters but our superclass is coded to assert their non-null-ness. **/
	public OperatingSystemPDFRunnable(final ProducePDFHandler handler, final IWorkbenchPartSite site, final IResource aSpecFile) {
		super(handler, site, aSpecFile);
	}

	public void run() {
        monitor.subTask("Opening PDF File");
        
		final String openCommand = "open " + outputFileName;
		try {
			Runtime.getRuntime().exec(openCommand);
		} catch (final Exception e) {
			TLA2TeXActivator.getDefault().logError("Unable to execute 'open' command on PDF.", e);
		}

        monitor.worked(1);
	}
}
