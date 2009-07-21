package org.lamport.tla.toolbox.ui.provider;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE.SharedImages;
import org.eclipse.ui.navigator.IDescriptionProvider;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;

/**
 * Label provider for all toolbox internal elements
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ToolboxLabelProvider 
extends LabelProvider implements ILabelProvider, IDescriptionProvider
{
    public String getText(Object element)
    {
        if (element == null) 
        {
            return null;
        }
        if (element instanceof Spec)
        {
            Spec spec = (Spec)element;
            return spec.getName() + " [ " +spec.getRootFile().getName() + " ]";
        } else if (element instanceof Module) 
        {
            return ((Module)element).getModuleName();
        } 
        return null;
    }

    public String getDescription(Object element)
    {
        String text = getText(element);
        return "This is a description of " + text;
    }
    
    public Image getImage(Object element)
    {
        if (element == null) 
        {
            return null;
        }
        if (element instanceof Spec) 
        {
            if (((Spec)element) == Activator.getSpecManager().getSpecLoaded()) 
            {
                return PlatformUI.getWorkbench().getSharedImages().getImage(SharedImages.IMG_OBJ_PROJECT);
            }
            return PlatformUI.getWorkbench().getSharedImages().getImage(SharedImages.IMG_OBJ_PROJECT_CLOSED);
        } else if (element instanceof Module) 
        {
            
            return PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJ_FILE);
        }
        return null;
    }
}