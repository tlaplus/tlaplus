package de.techjava.tla.ui.widgets;

import org.eclipse.core.resources.IProject;

/**
 * Interface for listener intersted in project selection
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: IProjectSelectionListener.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface IProjectSelectionListener 
{
    /**
     * Informs a listener that a project has been selected
     * @param project selected project
     */
    public void projectSelected(IProject project);
}

/*
 * $Log: IProjectSelectionListener.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:54:47  sza
 * running copy
 *
 *
 */