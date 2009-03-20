package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Vector;

import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class AssignmentContentProvider implements IStructuredContentProvider
{
    Object[] EMPTY = new Object[0];
    /* (non-Javadoc)
     * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
     */
    public Object[] getElements(Object inputElement)
    {
        if (inputElement != null && inputElement instanceof Vector) 
        {
            Vector equationList = (Vector) inputElement;
            return equationList.toArray(new Assignment[equationList.size()]);
        }
        return EMPTY;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.viewers.IContentProvider#dispose()
     */
    public void dispose()
    {
        
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.viewers.IContentProvider#inputChanged(org.eclipse.jface.viewers.Viewer, java.lang.Object, java.lang.Object)
     */
    public void inputChanged(Viewer viewer, Object oldInput, Object newInput)
    {
        
    }

}
