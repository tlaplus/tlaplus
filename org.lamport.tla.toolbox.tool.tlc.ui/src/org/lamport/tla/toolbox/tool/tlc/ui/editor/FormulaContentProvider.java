package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Vector;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.Viewer;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FormulaContentProvider implements IStructuredContentProvider
{
    private static final Object[] EMPTY = new Object[0];
    // private Vector formulaList;
    
    
    public FormulaContentProvider()
    {
        /*
        formulaList = new Vector();
        formulaList.add(new Formula("x = x + 1"));
        formulaList.add(new Formula("z = z + 1"));
        formulaList.add(new Formula("y = y + 1"));
        */

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
        /*
        if (newInput instanceof Vector)
        {
            formulaList = (Vector) newInput;
        }
        */ 
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
    
    
    public static class Formula
    {
        String formula;

        /**
         * @param string
         * @param b
         */
        public Formula(String formula)
        {
            this.formula = formula;
        }
        
        public String toString()
        {
            return formula;
        }
    }
}
