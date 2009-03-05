package de.techjava.tla.ui.extensions;

import java.util.Enumeration;

/**
 * Represents an error container
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: IProblemContainer.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface IProblemContainer 
{
    /**
     * Retrieves the enumeration of warnings
     * @return Enumeration of IProblemHolder
     */
    public Enumeration getWarnings();
    public Enumeration getErrors();
    public Enumeration getAborts();
    public boolean hasAborts();
    public boolean hasErrors();
    public boolean hasWarnings();

}

/*
 * $Log: IProblemContainer.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 *
 */