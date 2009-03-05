package de.techjava.tla.ui.util;

import java.util.Properties;
import java.util.StringTokenizer;

import org.eclipse.core.runtime.Path;
import org.eclipse.jface.preference.IPreferenceStore;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.extensions.ITLAParserConfiguration;

/**
 * A toolkit for TLA+ Syntactic Analyser libraries
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ParserManager.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class ParserManager 
	implements ITLASANYConstants
{
    private final static String PREFERENCE_DELIMITER 	= ";";
	private final static String VALUE_IDENTIFIER 		= "=";
	private final static String ENTRY_DELIMITER 		= ",";
	private final static String KEY_DELIMITER 			= ";";
    
    private IPreferenceStore store;

    /**
     * Constructor
     * 
     * @param store
     */
    public ParserManager(IPreferenceStore store) 
    {
		this.store = store;
	}

	/**
	 * Return the TLASANY system libriry paths preference as an array of
	 * Strings.
	 * @return Path[]
	 */
	public Path[] getLibraries() 
	{
        return convert(store.getString(TLA_SANY_LIBRARY));
	}

    /**
     * Retrieves default libraries
     * @return string array with library paths
	 */
	public Path[] getDefaultLibraries()
	{
	    String defaultLibrary = store.getDefaultString(TLA_SANY_LIBRARY);
	    String installedModules = UIPlugin.getDefault().getInstallationModulesPath();
		return convert(
		        defaultLibrary + ((installedModules == null) 
		                ? "" 
		                : PREFERENCE_DELIMITER + installedModules) );
    
	}
	/**
	 * Set the TLASANY system library paths preference
	 * @param String[] elements
	 */
	public void setLibraries(String[] elements)
	{
		StringBuffer buffer = new StringBuffer();
		for (int i = 0; i < elements.length; i++) {
			buffer.append(elements[i]);
			buffer.append(PREFERENCE_DELIMITER);
		}
		store.setValue(TLA_SANY_LIBRARY, buffer.toString());
	    
	}
    /**
     * Initialize default values
     */
    public void initializeDefaults()
    {
        store.setDefault(TLA_SANY_LIBRARY, DEFAULT_TLA_SANY_LIBRARY );
        store.setDefault(TLA_SANY_DO_DEBUGGING, DEFAULT_TLA_SANY_DO_DEBUGGING);
        store.setDefault(TLA_SANY_DO_LEVEL_CHECKING, DEFAULT_TLA_SANY_DO_LEVEL_CHECKING);
        store.setDefault(TLA_SANY_DO_SEMANTIC_ANALYSIS, DEFAULT_TLA_SANY_DO_SEMANTIC_ANALYSIS);
        store.setDefault(TLA_SANY_DO_STATS, DEFAULT_TLA_SANY_DO_STATS);
    }
    /**
     * Retrieves properties set by preference page
     * @return a property object containing the properties
     */
    public Properties getProperties() 
    {
        Properties properties = new Properties();
        properties.put(ITLAParserConfiguration.PARSER_CHECK_SEMANTIC, new Boolean(store.getBoolean(TLA_SANY_DO_SEMANTIC_ANALYSIS)));
        properties.put(ITLAParserConfiguration.PARSER_LEVEL_CHECK, new Boolean(store.getBoolean(TLA_SANY_DO_LEVEL_CHECKING)));
        properties.put(ITLAParserConfiguration.PARSER_BE_VERBOSE, new Boolean(store.getBoolean(TLA_SANY_DO_DEBUGGING)));
        properties.put(ITLAParserConfiguration.PARSER_GENERATE_STATS, new Boolean(store.getBoolean(TLA_SANY_DO_STATS)));
        return properties;
    }
	/**
	 * Convert the supplied PREFERENCE_DELIMITER delimited
	 * String to a Path array.
	 * @return Path[]
	 */
	private Path[] convert(String preferenceValue) 
	{
		StringTokenizer tokenizer = new StringTokenizer(preferenceValue, PREFERENCE_DELIMITER);
		int tokenCount = tokenizer.countTokens();
		
		Path[] elements = new Path[tokenCount];

		for (int i = 0; i < tokenCount; i++) {
			elements[i] = new Path(tokenizer.nextToken());
		}

		return elements;
	}


}

/*
 * $Log: ParserManager.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/13 09:46:02  sza
 * plugin integration
 *
 * Revision 1.2  2004/10/12 16:47:23  sza
 * removed compilation probelms
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
 * additions
 *
 * Revision 1.2  2004/10/07 00:06:27  sza
 * system libraries introduced
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:04  sza
 * initial commit
 *
 *
 */