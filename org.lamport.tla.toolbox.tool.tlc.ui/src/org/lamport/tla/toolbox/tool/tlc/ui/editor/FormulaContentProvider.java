package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FormulaContentProvider implements IStructuredContentProvider
{
    private static final Object[] EMPTY = new Object[0];
    
    public FormulaContentProvider()
    {
    }
    
    /* (non-Javadoc)
     * @see org.eclipse.jface.viewers.IContentProvider#dispose()
     */
    public void dispose()
    {
       //  formulaList = null;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.viewers.IContentProvider#inputChanged(org.eclipse.jface.viewers.Viewer, java.lang.Object, java.lang.Object)
     */
    public void inputChanged(Viewer viewer, Object oldInput, Object newInput)
    {
        Assert.isNotNull(viewer);
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
     */
    public Object[] getElements(Object inputElement)
    {
        if (inputElement != null && inputElement instanceof Vector) 
        {
            Vector formulaList = (Vector) inputElement;
            return formulaList.toArray(new Formula[formulaList.size()]);
        }
        return EMPTY;
    }
}
