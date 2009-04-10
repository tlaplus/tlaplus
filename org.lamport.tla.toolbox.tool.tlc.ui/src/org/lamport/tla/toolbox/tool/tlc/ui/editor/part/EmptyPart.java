package org.lamport.tla.toolbox.tool.tlc.ui.editor.part;

import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.AbstractFormPart;

/**
 * Empty part
 * @author Simon Zambrovski
 * @version $Id: EmptyPart.java 589 2009-03-18 16:53:13Z simonzam $
 */
public class EmptyPart extends AbstractFormPart
{
    private Vector controls = new Vector();
    
    public boolean addControl(Control control)
    {
        Assert.isNotNull(control);
        return controls.add(control);
    }

    public boolean removeControl(Control control)
    {
        Assert.isNotNull(control);
        return controls.remove(control);
    }

    /**
     * Tests if the control belongs to the part, providing a deep search 
     * for SWT composites
     * @param control
     * @return
     */
    public boolean isControlledBy(Control control)
    {
        Assert.isNotNull(control);
        boolean contains = controls.contains(control);
        
        if (!contains && control instanceof Composite)
        {
            Control[] children = ((Composite) control).getChildren();
            for (int i = 0; i < children.length; i++)
            {
                contains = isControlledBy(children[i]);
                if (contains)
                {
                    return true;
                }
            }
        }
        
        return contains;
    }
}
