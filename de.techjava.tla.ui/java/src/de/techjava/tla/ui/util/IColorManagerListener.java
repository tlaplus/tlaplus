package de.techjava.tla.ui.util;

/**
 * An interface for entities interesting in changes of color preferences
 * 
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: IColorManagerListener.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public interface IColorManagerListener 
{

    /**
     * Color preferences changed
     */
    void colorManagerChanged();
    
}

/*
 * $Log: IColorManagerListener.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/20 22:42:31  sza
 * editor improvements
 *
 *
 */