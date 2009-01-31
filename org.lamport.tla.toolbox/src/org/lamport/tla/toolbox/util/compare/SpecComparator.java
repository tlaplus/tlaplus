package org.lamport.tla.toolbox.util.compare;

import java.util.Comparator;

import org.lamport.tla.toolbox.spec.Spec;


/**
 *
 * @author zambrovski
 */
public class SpecComparator implements Comparator
{

    /**
     * Specifications are compared by comparison of the lastOpened date
     * 
     * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
     */
    public int compare(Object arg0, Object arg1)
    {
        if (arg0 == null || !(arg0 instanceof Spec) )
        {
            return 1;
        } else if (arg1 == null || !(arg1 instanceof Spec)) 
        {
            return -1;
        } else 
        {
            Spec s1 = (Spec) arg0;
            Spec s2 = (Spec) arg1;
            if (s1.getLastModified() == null && s2.getLastModified()!= null)
            {
                return 1;
            } else if (s2.getLastModified() == null && s1.getLastModified() != null)
            {
                return -1;
            } else if (s2.getLastModified() == null && s1.getLastModified() == null)
            {
                return 0;
            } else
            {
                return s1.getLastModified().compareTo(s2.getLastModified());
            }
        }

    }

}
