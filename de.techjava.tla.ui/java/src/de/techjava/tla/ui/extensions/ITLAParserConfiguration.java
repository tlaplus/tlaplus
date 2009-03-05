package de.techjava.tla.ui.extensions;

import java.util.Map;

import org.eclipse.core.runtime.IPath;

/**
 * Defines a parser configuration
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLAParserConfiguration.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface ITLAParserConfiguration 
{
    public final static String PARSER_CHECK_SEMANTIC 	= "ParserCheckSemantic";
    public final static String PARSER_BE_VERBOSE 		= "ParserBeVerbose";
    public final static String PARSER_GENERATE_STATS 	= "ParserGenerateStats";
    public final static String PARSER_LEVEL_CHECK 		= "ParserLevelCheck";
    
    public IPath[] getLibraryPath();

    public IPath getRootDirectory();
    
    public Map getSwitches();

    public void setLibraryPath(IPath[] paths);

    public void setRootDirectory(IPath path);

    public void setSwitches(Map properties);
    
}

/*
 * $Log: ITLAParserConfiguration.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 *
 */