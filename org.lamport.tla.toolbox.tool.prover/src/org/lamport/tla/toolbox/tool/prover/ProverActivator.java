package org.lamport.tla.toolbox.tool.prover;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Plugin;
import org.eclipse.core.runtime.Status;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class ProverActivator extends Plugin {

	// The plug-in ID
	public static final String PLUGIN_ID = "org.lamport.tla.toolbox.tool.prover";

	// The shared instance
	private static ProverActivator plugin;
	
	/**
	 * The constructor
	 */
	public ProverActivator() {
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugins#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.runtime.Plugin#stop(org.osgi.framework.BundleContext)
	 */
	public void stop(BundleContext context) throws Exception {
		plugin = null;
		super.stop(context);
	}

	/**
	 * Returns the shared instance
	 *
	 * @return the shared instance
	 */
	public static ProverActivator getDefault() {
		return plugin;
	}
	
	/**
     * Writes a string and a cause into the error category of the log
     * @param string
     * @param e
     */
    public static void logError(String message, Throwable cause)
    {
        getDefault().getLog().log(new Status(IStatus.ERROR, PLUGIN_ID, message, cause));
    }
    
    /**
     * Writes a string into some debugging place
     */
    public static void logDebug(String message)
    {
        System.out.println(message);
    }

}
