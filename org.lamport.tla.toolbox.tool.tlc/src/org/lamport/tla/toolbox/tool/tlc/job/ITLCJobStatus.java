package org.lamport.tla.toolbox.tool.tlc.job;

import java.net.URL;

import org.eclipse.core.runtime.IStatus;

public interface ITLCJobStatus extends IStatus {

	URL getURL();

}
