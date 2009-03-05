package de.techjava.tla.ui.extensions;

import java.util.Map;

import org.eclipse.core.resources.IProject;

/**
 * Basic interface for TLA+ Parser Runtime Extension
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ITLAParserRuntime.java,v 1.3 2007/07/04 08:54:45 dan_nguyen Exp $
 */
public interface ITLAParserRuntime 
{
	
	
    /**
     * Initialize the parsering of TLA files
     * 
     * @param resourceNames Array containing resource names relative to source root
     * @param project		Project the compilation is being executed upon
     * 
     * @return array containing the results in order corresponding to input files 
     */
    public ITLAParserResult[] parse(String[] resourceNames, IProject project );
    /**
     * Flushes the parser cache
     */
           
    public void flush();
    
    /**
	 * dannm added
	 * Get the SpecObj array after the tla specification has been parsed
	 * This SpecObj will provide the SyntaxTreeNode object which serves as the model for the Outline View 
	 * @return
	 */	
    public Map getSpecObj();
}

/*
 * $Log: ITLAParserRuntime.java,v $
 * Revision 1.3  2007/07/04 08:54:45  dan_nguyen
 * remove unused comments
 *
 * Revision 1.2  2007/06/27 15:34:46  dan_nguyen
 * changes for tla editor outline view
 *
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/10/20 17:57:39  bgr
 * incremental build functionality started
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 *
 */
