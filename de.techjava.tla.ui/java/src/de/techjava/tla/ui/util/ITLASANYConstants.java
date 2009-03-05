package de.techjava.tla.ui.util;



/**
 * Constants for SANY
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLASANYConstants.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public interface ITLASANYConstants 
{
    public final static String	TLA_SANY_LIBRARY 				= "__TLA_SANY_SystemLibraries";
    public static final String 	TLA_SANY_DO_SEMANTIC_ANALYSIS	= "__TLA_SANY_DoSemanticAnalysisPreference";
    public static final String 	TLA_SANY_DO_LEVEL_CHECKING		= "__TLA_SANY_DoLevelCheckingPreference";
    public static final String 	TLA_SANY_DO_DEBUGGING			= "__TLA_SANY_DoDebuggingPreference";
    public static final String 	TLA_SANY_DO_STATS				= "__TLA_SANY_DoStatsPreference";

    
    
    public final static boolean DEFAULT_TLA_SANY_DO_SEMANTIC_ANALYSIS 	= true;
    public final static boolean DEFAULT_TLA_SANY_DO_LEVEL_CHECKING 		= true;
    public final static boolean DEFAULT_TLA_SANY_DO_DEBUGGING 			= false;
    public final static boolean DEFAULT_TLA_SANY_DO_STATS 				= false;
    public final static String 	DEFAULT_TLA_SANY_LIBRARY 				= "";
}

/*
 * $Log: ITLASANYConstants.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
 * additions
 *
 * Revision 1.2  2004/10/07 00:06:06  sza
 * changed default values
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:04  sza
 * initial commit
 *
 *
 */