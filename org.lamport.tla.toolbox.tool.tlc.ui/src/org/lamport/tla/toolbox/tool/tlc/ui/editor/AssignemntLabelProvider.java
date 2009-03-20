package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class AssignemntLabelProvider extends LabelProvider implements ITableLabelProvider
{

    /* (non-Javadoc)
     * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnImage(java.lang.Object, int)
     */
    public Image getColumnImage(Object element, int columnIndex)
    {
        return null;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnText(java.lang.Object, int)
     */
    public String getColumnText(Object element, int columnIndex)
    {
        if (element != null && element instanceof Assignment) 
        {
            Assignment assign = (Assignment) element;
            switch (columnIndex) 
            {
            case 0:
                return assign.getLeft();
            case 1:
                return assign.getRight();
            }
        }
        return null;
    }
}
