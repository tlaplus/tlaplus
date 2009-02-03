package org.lamport.tla.toolbox.util.compare;

import java.util.Comparator;

import org.eclipse.core.resources.IResource;

/**
 * Compare resources based on the name, ignoring the case
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResourceNameComparator implements Comparator
{

    /* (non-Javadoc)
     * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
     */
    public int compare(Object arg0, Object arg1)
    {
        if (arg0 == null || !(arg0 instanceof IResource) )
        {
            return 1;
        } else if (arg1 == null || !(arg1 instanceof IResource))
        {
            return -1;
        } else 
        {
            IResource m1 = (IResource) arg0;
            IResource m2 = (IResource) arg1;
            
            return m1.getName().compareToIgnoreCase(m2.getName());
        }
        
    }

}
