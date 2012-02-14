// Copyright (c) Feb 13, 2012 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.plugin.AbstractUIPlugin;

/**
 * @author Markus Alexander Kuppe
 */
public abstract class AbstractTLCActivator extends AbstractUIPlugin {

	private static final int DEBUG_SEVERITY = -1;
	private final String pluginId;

	public AbstractTLCActivator(final String pluginId) {
		this.pluginId = pluginId;
	}

	/**
	 * Writes a string and a cause into the error category of the log
	 * 
	 * @param string
	 */
	public void logError(String message) {
		getLog().log(new Status(IStatus.ERROR, pluginId, message));
	}
	
	/**
	 * Writes a string and a cause into the error category of the log
	 * 
	 * @param string
	 * @param e
	 */
	public void logError(String message, Throwable cause) {
		getLog().log(new Status(IStatus.ERROR, pluginId, message, cause));
	}

	/**
	 * Writes a string and a cause into the warning category of the log
	 * 
	 * @param string
	 */
	public void logWarning(String message) {
		getLog().log(new Status(IStatus.WARNING, pluginId, message));
	}

	/**
	 * Writes a string and a cause into the warning category of the log
	 * 
	 * @param string
	 */
	public void logWarning(String message, Throwable cause) {
		getLog().log(new Status(IStatus.WARNING, pluginId, message, cause));
	}

	/**
	 * Writes a string into some debugging place
	 */
	public void logDebug(String message) {
		logDebug(message, null);
	}

	/**
	 * Writes a string into some debugging place
	 */
	public void logDebug(String message, Throwable cause) {
		getLog().log(new Status(IStatus.INFO, pluginId, DEBUG_SEVERITY, message, cause));
	}

	/**
	 * Writes a string into the info category of the log
	 * 
	 * @param string
	 */
	public void logInfo(String message) {
		getLog().log(new Status(IStatus.INFO, pluginId, message));
	}
}
