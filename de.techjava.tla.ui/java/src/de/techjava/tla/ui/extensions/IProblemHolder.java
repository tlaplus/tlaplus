package de.techjava.tla.ui.extensions;

/**
 * Problem holder interface
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: IProblemHolder.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface IProblemHolder 
{
    public final static int ABORT 		= 1;
    public final static int ERROR 		= 2;
    public final static int WARNING 	= 3;

    /**
     * Retrieves the problem location
     * @return
     */
    public ILocation getLocation();
    /**
     * Retrieves the problem type
     */
    public int getType();
    /**
     * Retrieves the message
     * @return
     */
    public String getMessage();
    
}

/*
 * $Log: IProblemHolder.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 *
 */