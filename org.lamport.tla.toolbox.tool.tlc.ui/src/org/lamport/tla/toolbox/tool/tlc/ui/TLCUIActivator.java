package org.lamport.tla.toolbox.tool.tlc.ui;

import org.eclipse.core.runtime.Status;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.ui.plugin.AbstractUIPlugin;
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.framework.BundleContext;

/**
 * The activator class controls the plug-in life cycle
 */
public class TLCUIActivator extends AbstractUIPlugin
{
    // The plug-in ID
    public static final String PLUGIN_ID = "org.lamport.tla.toolbox.tool.tlc.ui";

    // The shared instance
    private static TLCUIActivator plugin;

    private Font courierFont;
    private Font outputFont;

    // update the CNF content
    /*
    private PerspectiveAdapter perspectiveAdapter = new PerspectiveAdapter() 
    {
        public void perspectiveActivated(IWorkbenchPage page, IPerspectiveDescriptor perspective)
        {
            if (TLCPerspective.ID.equals(perspective.getId()))
            {
                ToolboxHandle.setToolboxNCEActive(ModelContentProvider.TLC_NCE, true);
            }
        }

        public void perspectiveDeactivated(IWorkbenchPage page, IPerspectiveDescriptor perspective)
        {
            if (TLCPerspective.ID.equals(perspective.getId()))
            {
                ToolboxHandle.setToolboxNCEActive(ModelContentProvider.TLC_NCE, false);
            }
        }
    };
    */

    /**
     * The constructor
     */
    public TLCUIActivator()
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

        /*
        IWorkbenchWindow window = UIHelper.getActiveWindow();
        if (window != null)
        {
            window.addPerspectiveListener(perspectiveAdapter);
        }*/
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#stop(org.osgi.framework.BundleContext)
     */
    public void stop(BundleContext context) throws Exception
    {
        // IWorkbenchWindow window = UIHelper.getActiveWindow();
        /*
        if (window != null)
        {
            window.removePerspectiveListener(perspectiveAdapter);
        }*/
        if (courierFont != null)
        {
            courierFont.dispose();
        }
        if (outputFont != null)
        {
            outputFont.dispose();
        }
        plugin = null;
        super.stop(context);
    }

    /**
     * Returns the shared instance
     *
     * @return the shared instance
     */
    public static TLCUIActivator getDefault()
    {
        return plugin;
    }

    public synchronized Font getCourierFont()
    {
        if (courierFont == null)
        {
            courierFont = new Font(UIHelper.getShellProvider().getShell().getDisplay(), "Courier New", 11, SWT.NORMAL);
        }
        return courierFont;
    }

    /**
     * @return
     */
    public Font getOutputFont()
    {
        if (outputFont == null)
        {
            outputFont = new Font(UIHelper.getShellProvider().getShell().getDisplay(), "Courier New", 8, SWT.NORMAL);
        }
        return outputFont;
    }

    /**
     * Returns an image descriptor for the image file at the given
     * plug-in relative path
     *
     * @param path the path
     * @return the image descriptor
     */
    public static ImageDescriptor getImageDescriptor(String path)
    {
        return imageDescriptorFromPlugin(PLUGIN_ID, path);
    }

    /**
     * Logs an error
     * @param message
     * @param e 
     */
    public static void logError(String message, Throwable e)
    {
        getDefault().getLog().log(new Status(Status.ERROR, TLCUIActivator.PLUGIN_ID, message, e));
    }

    /**
     * @param string
     */
    public static void logDebug(String string)
    {
        System.out.println(string);
    }

}
