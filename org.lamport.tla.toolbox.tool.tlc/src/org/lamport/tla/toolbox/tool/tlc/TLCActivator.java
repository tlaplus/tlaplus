package org.lamport.tla.toolbox.tool.tlc;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.lamport.tla.toolbox.tool.IToolboxContribution;
import org.lamport.tla.toolbox.tool.ToolInitializationException;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class TLCActivator extends AbstractUIPlugin implements IToolboxContribution {

	// The plug-in ID
	public static final String PLUGIN_ID = "org.lamport.tla.toolbox.tool.tlc";

	// The shared instance
	private static TLCActivator plugin;
	
	/**
	 * The constructor
	 */
	public TLCActivator() {
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
	 * Returns an image descriptor for the image file at the given
	 * plug-in relative path
	 *
	 * @param path the path
	 * @return the image descriptor
	 */
	public static ImageDescriptor getImageDescriptor(String path) {
		return imageDescriptorFromPlugin(PLUGIN_ID, path);
	}

    /** 
     * Life cycle method executed by the toolbox 
     * @see org.lamport.tla.toolbox.tool.IToolboxContribution#initialize()
     */
    public void initialize() throws ToolInitializationException
    {
        System.out.println("we are initilized!");
        
    }

    /** 
     * Life cycle method executed by the toolbox
     * @see org.lamport.tla.toolbox.tool.IToolboxContribution#terminate()
     */
    public void terminate() throws ToolInitializationException
    {
        System.out.println("we are terminated!");
        
    }
}
