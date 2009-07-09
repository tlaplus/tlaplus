package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.navigator.IDescriptionProvider;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Provides labels for the TLC models
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelLabelProvider extends LabelProvider implements IDescriptionProvider
{
    private Image image = TLCActivator.getImageDescriptor("/icons/full/choice_sc_obj.gif").createImage();

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
                if (ModelHelper.isModelLocked(config)) 
                {
                    return modelName + " [ modelchecking ]";
                }
            } catch (CoreException e)
            {
                // TODO
                e.printStackTrace();
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
