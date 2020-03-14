// Copyright (c) Feb 13, 2012 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.ui.plugin.AbstractUIPlugin;

/**
 * @author Markus Alexander Kuppe
 */
public class StandaloneActivator extends AbstractUIPlugin {

	private static final int DEBUG_SEVERITY = -1;
	public static final String PLUGIN_ID = "org.lamport.tla.toolbox.product.standalone";
	private static StandaloneActivator plugin;
	
	public StandaloneActivator() {
		plugin = this;
	}

	/**
	 * Returns the shared instance
	 * 
	 * @return the shared instance
	 */
	public static StandaloneActivator getDefault() {
		return plugin;
	}

	/**
	 * Writes a string and a cause into the error category of the log
	 * 
	 * @param string
	 */
	public void logError(String message) {
		getLog().log(new Status(IStatus.ERROR, PLUGIN_ID, message));
	}
	
	/**
	 * Writes a string and a cause into the error category of the log
	 * 
	 * @param string
	 * @param e
	 */
	public void logError(String message, Throwable cause) {
		getLog().log(new Status(IStatus.ERROR, PLUGIN_ID, message, cause));
	}

	/**
	 * Writes a string and a cause into the warning category of the log
	 * 
	 * @param string
	 */
	public void logWarning(String message) {
		getLog().log(new Status(IStatus.WARNING, PLUGIN_ID, message));
	}

	/**
	 * Writes a string and a cause into the warning category of the log
	 * 
	 * @param string
	 */
	public void logWarning(String message, Throwable cause) {
		getLog().log(new Status(IStatus.WARNING, PLUGIN_ID, message, cause));
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
		getLog().log(new Status(IStatus.INFO, PLUGIN_ID, DEBUG_SEVERITY, message, cause));
	}

	/**
	 * Writes a string into the info category of the log
	 * 
	 * @param string
	 */
	public void logInfo(String message) {
		getLog().log(new Status(IStatus.INFO, PLUGIN_ID, message));
	}
}
