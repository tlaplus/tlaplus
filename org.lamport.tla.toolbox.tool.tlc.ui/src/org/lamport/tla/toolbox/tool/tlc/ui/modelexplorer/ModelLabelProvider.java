package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.navigator.IDescriptionProvider;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Provides labels for the TLC models
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelLabelProvider extends LabelProvider implements IDescriptionProvider
{
    private Image image = TLCUIActivator.getImageDescriptor("/icons/full/choice_sc_obj.gif").createImage();
    private ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();

    /**
     * Retrieves model's image
     */
    public Image getImage(Object element)
    {
        if (element instanceof ILaunchConfiguration)
        {
            return image;
        }
        return super.getImage(element);
    }

    /**
     * Retrieves model's label 
     */
    public String getText(Object element)
    {
        if (element instanceof ILaunchConfiguration)
        {
            ILaunchConfiguration config = (ILaunchConfiguration) element;
            String modelName = ModelHelper.getModelName(config.getFile());
            try
            {
                if (ModelHelper.isModelStale(config))
                {
                    return modelName + " [ crashed ]";
                }
                if (ModelHelper.isModelRunning(config))
                {
                    ILaunch[] launches = launchManager.getLaunches();
                    boolean found = false;
                    for (int i = 0; i < launches.length; i++)
                    {
                        if (launches[i].getLaunchConfiguration().contentsEqual(config))
                        {
                            found = true;
                            break;
                        }
                    }
                    if (found)
                    {
                        return modelName + " [ modelchecking ]";
                    } else
                    {
                        // the MC crashed
                        // mark the error
                        ModelHelper.staleModel(config);
                        return modelName + " [ crashed ]";
                    }
                }
            } catch (CoreException e)
            {
                TLCUIActivator.logError("Error creating description for a model", e);
            }
            return modelName;
        }
        return null;
    }

    /**
     * Description to be shown in the status bar
     */
    public String getDescription(Object element)
    {
        if (element instanceof ILaunchConfiguration)
        {
            return getText(element);
        }
        return null;

    }

    /**
     * Dispose the image
     */
    public void dispose()
    {
        if (image != null)
        {
            image.dispose();
        }
        image = null;
        super.dispose();
    }

}
