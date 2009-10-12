package org.lamport.tla.toolbox.util.compare;

import java.util.Comparator;

import org.eclipse.core.runtime.CoreException;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.handler.CloseSpecHandler;

/**
 *
 * @author zambrovski
 */
public class SpecComparator implements Comparator
{

    /**
     * Specifications are compared by comparison of when they were last
     * closed, with compare(spec1, spec2) returning +1 iff spec1 was
     * last closed before spec2 was.  As far as I know, this is used
     * only for ordering the specs in the Open Spec menu.  
     *     Changed by LL and Dan R on 12 October 2009
     * 
     * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
     */
    public int compare(Object arg0, Object arg1)
    {
        if (arg0 == null || !(arg0 instanceof Spec))
        {
            return 1;
        } else if (arg1 == null || !(arg1 instanceof Spec))
        {
            return -1;
        } else
        {
            Spec s1 = (Spec) arg0;
            Spec s2 = (Spec) arg1;
            long s1Time = getLastClosedTime(s1);
            long s2Time = getLastClosedTime(s2);
            if (s1Time == s2Time)
            {
                return 0;
            } else if (s1Time > s2Time)
            {
                return -1;
            } else
            {
                return 1;
            }
        }
        // if (s1.getLastModified() == null && s2.getLastModified()!= null)
        // {
        // return 1;
        // } else if (s2.getLastModified() == null && s1.getLastModified() != null)
        // {
        // return -1;
        // } else if (s2.getLastModified() == null && s1.getLastModified() == null)
        // {
        // return 0;
        // } else
        // {
        // return s1.getLastModified().compareTo(s2.getLastModified());
        // }
    }

    /**
     * Returns the time spec Spec was last closed.
     * @param spec
     * @return
     */
    private long getLastClosedTime(Spec spec)
    {
        try
        {
            String timeAsString = spec.getProject().getPersistentProperty(CloseSpecHandler.LAST_CLOSED_DATE);
            if (timeAsString == null)
            { 
                // This value may be null if the user has just created
                // the spec and not yet closed it when he clicks on the Open
                // Spec menu.  (I'm not sure.)  LL
                // Activator.logDebug("Null read as LAST_CLOSED_DATE.");
                return 0;
            }
            return Long.parseLong(timeAsString);

        } catch (CoreException e)
        {
            Activator.logDebug("Exception thrown when reading project LAST_CLOSED time.");
            return 0;
        }
    }

}
