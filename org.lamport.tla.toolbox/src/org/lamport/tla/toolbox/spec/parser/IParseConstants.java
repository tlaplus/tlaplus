package org.lamport.tla.toolbox.spec.parser;

/**
 * Parse constants (must be in the descending order)
 * @author zambrovski
 * @version $Id$
 */
public interface IParseConstants
{
    /** PARSED = no SANY error */ 
    public static final int PARSED                = 0;
    /** SEMANTIC_WARNING = warnings were produced, but no error. */ 
    public static final int SEMANTIC_WARNING      = -1;
    /** SEMANTIC_ERROR = an error in semantic processing */
    public static final int SEMANTIC_ERROR        = -2;
    /** SYNTAX_ERROR = a parsing error */
    public static final int SYNTAX_ERROR          = -3;
    /** UNKNOWN_ERROR = SANY.frontEndInitialize returned an error, indicating some serious problem that I don't understand. */
    public static final int UNKNOWN_ERROR         = -4;
    /** COULD_NOT_FIND_MODULE = the root module was not found. */
    public static final int COULD_NOT_FIND_MODULE = -5;
    /** MODIFIED = the module has been parsed but has been modified after the last parse */ 
    public static final int MODIFIED              = -98;
    /** UNPARSED = the root module was not parsed */
    public static final int UNPARSED              = -99;
    /** UNKNOW status - the spec is not loaded  */
    public static final int UNKNOWN               = -100;
    
}