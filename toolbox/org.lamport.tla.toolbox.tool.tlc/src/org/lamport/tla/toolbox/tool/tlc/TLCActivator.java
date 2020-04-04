package org.lamport.tla.toolbox.tool.tlc;

import org.eclipse.core.runtime.Status;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class TLCActivator extends AbstractUIPlugin {
	
    // TODO This is the only constant used in our Preferences that is not declared in ITLCPreferenceConstants
    //          because of package dependency issues. We should do something about that because this scattering
    //          feels meh.
	/**
     * This preference is exposed through the Toolbox preference pane and allows the
     * user to dictate how many snapshots are kept (with the oldest being pruned as
     * this value is reached or exceeded.)  A value of 0 here means that no snapshot
     * is taken as part of the pre-launch of TLC.
	 */
    public static final String I_TLC_SNAPSHOT_KEEP_COUNT = "numberOfSnapshotsToKeep";
	
	// The plug-in ID
	public static final String PLUGIN_ID = "org.lamport.tla.toolbox.tool.tlc";

	// The shared instance
	private static TLCActivator plugin;
	
	/**
	 * The constructor
	 */
	public TLCActivator() 
	{
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
	 */
	public void start(BundleContext context) throws Exception {
		super.start(context);
		plugin = this;
	}

	/*
	 * (non-Javadoc)
	 * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
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
	public static TLCActivator getDefault() {
		return plugin;
	}

    /**
     * Logs an error
     * @param message
     * @param e 
     */
    public static void logError(String message, Throwable e)
    {
        getDefault().getLog().log(new Status(Status.ERROR, TLCActivator.PLUGIN_ID, message, e));
    }

    /**
     * Prints a debug message
     * @param message to print
     */
    public static void logInfo(String message)
    {
        getDefault().getLog().log(new Status(Status.INFO, TLCActivator.PLUGIN_ID, message));
    }
    
    /**
     * Prints a debug message
     * @param message to print
     */
    public static void logDebug(String message)
    {
        System.out.println(message);
    }

}
