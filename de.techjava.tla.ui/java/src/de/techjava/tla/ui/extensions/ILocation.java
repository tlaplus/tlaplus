package de.techjava.tla.ui.extensions;

/**
 * A location
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ILocation.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface ILocation 
{
    /**
     * Indicates that current location is a null clocation
     * @return
     */
    public boolean isNullLocation();
    
    /** 
     * gets the begin line number of this location. 
     */
    public int beginLine();

    /** 
     * gets the begin column number of this location. 
     */
    public int beginColumn(); 

    /** 
     * gets the end line number of this location. 
     */
    public int endLine();
   
    /** 
     * gets the end column number of this location. 
     */
    public int endColumn();

    /** 
     * gets the file name of this location. 
     */
    public String source();
}

/*
 * $Log: ILocation.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 *
 */