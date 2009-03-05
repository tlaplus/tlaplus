package de.techjava.tla.ui.util;

import org.eclipse.swt.graphics.RGB;

/**
 * Encapsulate console settings
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLAConsoleConstants.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public interface ITLAConsoleConstants {

    public final static String SHOW_IN_CONSOLE 				= "__ShowInConsole";
    public static final String CONSOLE_PARSER_COLOR 		= "__ConsoleColorParser";
    public static final String CONSOLE_CHECKER_COLOR 		= "__ConsoleColorChecker";
    
    public final static RGB DEFAULT_CONSOLE_PARSER_COLOR 	= new RGB(127, 159, 127);
    public final static RGB DEFAULT_CONSOLE_CHECKER_COLOR 	= new RGB(127, 	 0,  85);

}

/*
 * $Log: ITLAConsoleConstants.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.3  2004/10/24 23:12:14  sza
 * new colors for console added
 *
 * Revision 1.2  2004/10/23 16:10:35  sza
 * new colors
 *
 * Revision 1.1  2004/10/19 15:39:24  sza
 * *** empty log message ***
 *
 *
 */