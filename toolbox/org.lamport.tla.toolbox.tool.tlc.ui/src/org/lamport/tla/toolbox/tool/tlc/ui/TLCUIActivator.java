package org.lamport.tla.toolbox.tool.tlc.ui;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.progress.UIJob;
import org.lamport.tla.toolbox.AbstractTLCActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ExecutionStatisticsDialog;
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.framework.BundleContext;

import util.ExecutionStatisticsCollector;

/**
 * The activator class controls the plug-in life cycle
 */
public class TLCUIActivator extends AbstractTLCActivator
{
    // The plug-in ID
    public static final String PLUGIN_ID = "org.lamport.tla.toolbox.tool.tlc.ui";

    // The shared instance
    private static TLCUIActivator plugin;

    private Font courierFont;
    private Font outputFont;

    /*
     * The colors used for trace row highlighting. These should be in some
     * central location containing all colors and fonts to make it easy to
     * make them changeable by preferences.
     */
    private Color changedColor;
    private Color addedColor;
    private Color deletedColor;

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
    	super(PLUGIN_ID);
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.plugin.AbstractUIPlugin#start(org.osgi.framework.BundleContext)
     */
    public void start(BundleContext context) throws Exception
    {
        super.start(context);
        plugin = this;

        changedColor = new Color(null, 255, 200, 200);
        addedColor = new Color(null, 255, 255, 200);
        deletedColor = new Color(null, 240, 240, 255);
        

		if (Display.getCurrent() != null && ExecutionStatisticsCollector.promptUser()) { // Display is null during unit test execution.
			final UIJob j = new UIJob(Display.getCurrent(), "TLA+ execution statistics approval.") {
				@Override
				public IStatus runInUIThread(final IProgressMonitor monitor) {
					new ExecutionStatisticsDialog(false, PlatformUI.createDisplay().getActiveShell()).open();
					return Status.OK_STATUS;
				}
			};
			j.schedule(5 * 60 * 1000L);
		}
    }

    public Color getChangedColor()
    {
        return changedColor;
    }


    public Color getAddedColor()
    {
        return addedColor;
    }


    public Color getDeletedColor()
    {
        return deletedColor;
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
        
        /*
         * Remove the colors
         */
        addedColor.dispose();
        changedColor.dispose();
        deletedColor.dispose();

        
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
     * @param colorRed
     * @return
     */
    public static Color getColor(int color)
    {
        return UIHelper.getShellProvider().getShell().getDisplay().getSystemColor(color);
    }
}
