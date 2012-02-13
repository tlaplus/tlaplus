// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox.tool.tla2tex.handler;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.util.ResourceHelper;

public abstract class AbstractPDFViewerRunnable implements Runnable {

	protected IFile outputFile;
	protected long translationStartTime;
	protected IProgressMonitor monitor;
	protected String outputFileName;

	public void setFile(String outputFileName) {
        this.outputFileName = outputFileName;
		this.outputFile = (IFile) ResourceHelper.getResourceByName(outputFileName);
	}
	
	public void setStartTime(long translationStartTime) {
		this.translationStartTime = translationStartTime;
	}

	public void setMonitor(IProgressMonitor monitor) {
		this.monitor = monitor;
	}
}
