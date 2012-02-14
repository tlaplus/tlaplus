// Copyright (c) Feb 13, 2012 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox;

/**
 * @author Markus Alexander Kuppe
 */
public class StandaloneActivator extends AbstractTLCActivator {

	public static final String PLUGIN_ID = "org.lamport.tla.toolbox.product.standalone";
	private static StandaloneActivator plugin;
	
	public StandaloneActivator() {
		super(PLUGIN_ID);
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
}
