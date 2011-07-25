package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.ITokenScanner;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.lamport.tla.toolbox.editor.basic.tla.TLACodeScanner;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class TLAEditorActivator extends AbstractUIPlugin
{

    // The plug-in ID
    public static final String PLUGIN_ID = "org.lamport.tla.toolbox.editor.basic";

    // The shared instance
    private static TLAEditorActivator plugin;

    // token scanner
    private TLAPartitionScanner partitionTokenScanner;
    private TLAColorProvider colorProvider;
    private TLACodeScanner tlaCodeScanner;

    /**
     * The constructor
     */
    public TLAEditorActivator()
    {
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
     */
    public void start(BundleContext context) throws Exception
    {
    	plugin = this;
        super.start(context);
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
    public static TLAEditorActivator getDefault()
    {
        return plugin;
    }

    /**
     * @return
     */
    public IPartitionTokenScanner getTLAPartitionScanner()
    {
        if (partitionTokenScanner == null) 
        {
            partitionTokenScanner = new TLAPartitionScanner();
        }
        return partitionTokenScanner; 
    }

    /**
     * @return
     */
    public TLAColorProvider getTLAColorProvider()
    {
        if (colorProvider == null) 
        {
            colorProvider = new TLAColorProvider();
        }
        return colorProvider; 
    }

    /**
     * @return
     */
    public ITokenScanner getTLACodeScanner()
    {
        if (tlaCodeScanner== null) 
        {
            tlaCodeScanner = new TLACodeScanner();
        }
        return tlaCodeScanner; 
    }
}
