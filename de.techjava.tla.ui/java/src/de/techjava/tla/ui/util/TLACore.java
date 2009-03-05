package de.techjava.tla.ui.util;

import java.util.Iterator;
import java.util.LinkedList;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.natures.TLANature;

/**
 * core utilities
 * 
 * @author Boris Gruschko, <a href="http://gruschko.org">http://gruschko.org</a> 
 * @version $Id: TLACore.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class TLACore {
    public static IProject[] getTLAProjects()
    {
        IProject[] projects = UIPlugin.getWorkspace().getRoot().getProjects();
    
        LinkedList res = new LinkedList();
        
        for ( int i = 0; i < projects.length; i++ )
        {
            try {
                if ( projects[i].hasNature( TLANature.NATURE_ID )  )
                    res.add( projects[i] );
            } catch (CoreException e) {
                e.printStackTrace();
            }
        }

        IProject[] ret = new IProject[res.size()];
        
        int j = 0;
        for ( Iterator i = res.iterator();i.hasNext(); j++ )
            ret[j] = (IProject) i.next();
        
        return ret;
    }

    /**
     * Retrieves a project by name
     * @param projectName
     */
    public static IProject getProjectByName(String projectName) 
    {
        IProject[] projects = UIPlugin.getWorkspace().getRoot().getProjects();
        for ( int i = 0; i < projects.length; i++ )
        {
            try {
                if ( projects[i].getName().equals(projectName) 
                        && projects[i].hasNature( TLANature.NATURE_ID ) )
                {
                    return projects[i];
                }
            } catch (CoreException e) {
                e.printStackTrace();
            }
        }
        return null;
    }
    
}

/*
 * $Log: TLACore.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/10/13 10:50:56  bgr
 * ids changed
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.2  2004/10/12 09:54:47  sza
 * running copy
 *
 * Revision 1.1  2004/10/11 19:39:43  bgr
 * initial load
 *
 *
 */