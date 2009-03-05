package de.techjava.tla.ui.util;

/**
 * Encapsulate constant cales for a project
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLAProjectConstants.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public interface ITLAProjectConstants 
{
	public static final String TLA_FILE_EXTENSION = "tla";
	public static final String CFG_FILE_EXTENSION = "cfg";

    

    public static final String PERSIST_PROJECT_SOURCE_FOLDER 					= "SourceDirectory";
    public static final String PERSIST_PROJECT_WORKING_FOLDER 					= "WorkingDirectory";
    public static final String PERSIST_PROJECT_CONFIG_FOLDER 					= "ConfigDirectory";
    public final static String PERSIST_PROJECT_LAYOUT_SEPARATED 				= "IsSourceAndConfigSeparated";
    
    public final static String TLA_PROJECT_LAYOUT_SEPARATED						= "__TLA_PROJECT_LAYOUT_SEPARATED";
    public final static String TLA_PROJECT_LAYOUT_SEPARATED_SOURCEDIR 			= "__TLA_PROJECT_LAYOUT_SEPARATED_SOURCEDIR";
    public final static String TLA_PROJECT_LAYOUT_SEPARATED_CONFIGDIR 			= "__TLA_PROJECT_LAYOUT_SEPARATED_CONFIGDIR";
    public final static String TLA_PROJECT_LAYOUT_WORKINGDIR 					= "__TLA_PROJECT_LAYOUT_WORKINGDIR";
    
    public final static boolean DEFAULT_TLA_PROJECT_LAYOUT_SEPARATED 			= false;
    public final static String DEFAULT_TLA_PROJECT_LAYOUT_SEPARATED_SOURCEDIR 	= "src";
    public final static String DEFAULT_TLA_PROJECT_LAYOUT_SEPARATED_CONFIGDIR 	= "config";
    public final static String DEFAULT_TLA_PROJECT_LAYOUT_WORKINGDIR 			= "work";
    public static final String DEFAULT_ROOT_FOLDER 								= "";
    
    
}

/*
 * $Log: ITLAProjectConstants.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.6  2004/10/25 16:50:31  sza
 * constants for extension added
 *
 * Revision 1.5  2004/10/15 01:16:53  sza
 * working directory added
 *
 * Revision 1.4  2004/10/15 00:38:55  sza
 * default value added
 *
 * Revision 1.3  2004/10/15 00:29:28  sza
 * working directory added
 *
 * Revision 1.2  2004/10/13 14:43:30  sza
 * persistent properties changed
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:11  sza
 * additions
 *
 *
 */