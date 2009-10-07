package org.lamport.tla.toolbox.tool.tla2tex;

import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class TLA2TeXActivator extends AbstractUIPlugin
{

    // The plug-in ID
    public static final String PLUGIN_ID = "org.lamport.tla.toolbox.tool.tlatex";

    // The shared instance
    private static TLA2TeXActivator plugin;

    /**
     * The constructor
     */
    public TLA2TeXActivator()
    {
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
     */
    public void start(BundleContext context) throws Exception
    {
        super.start(context);
        plugin = this;
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
     */
    public void stop(BundleContext context) throws Exception
    {
        plugin = null;
        super.stop(context);
    }

    /**
     * Returns the shared instance
     *
     * @return the shared instance
     */
    public static TLA2TeXActivator getDefault()
    {
        return plugin;
    }

}
