package org.lamport.tla.toolbox.util.pref;

/**
 *
 * @author zambrovski
 */
public interface IPreferenceConstants
{
    public static final String DEFAULT_NOT_SET                = "not set";

    
    /**
     * Project preference storing the root file
     */
    public static final String P_PROJECT_ROOT_FILE      = "ProjectRootFile";
    /**
     * Popup parser errors
     */
    public static final String I_PARSER_POPUP_ERRORS        = "parserPopupErrors";
    /**
     * Popup PCal errors
     */
    public static final String I_TRANSLATE_POPUP_ERRORS     = "translatorPopupErrors";
    /** 
     * restore the same state of the specification after a restart
     */
    public static final String I_RESTORE_LAST_SPEC          = "restoreLastSpec";
    /**
     * The minimum amount of storage used by the spec (in kbytes) for that
     * size to be displayed (on the bottom line, next to the parse status).
     */
    public static final String I_MIN_DISPLAYED_SIZE          = "minDisplayedSize";
    /**
     * Re-parse root on modify
     */
    public static final String I_PARSE_FILES_ON_MODIFY      = "autoParseTopModules";
    /**
     * Re-parse dependent modules on modify 
     */
    public static final String I_PARSE_MODULE_ON_MODIFY     = "autoParseModule";
    /**
     * Re-parse spec on modify
     */
    public static final String I_PARSE_SPEC_ON_MODIFY       = "autoParseSpec";
    /**
     * Re-translate module on modify
     */
    public static final String I_TRANSLATE_MODULE_ON_MODIFY = "autoTranslateModule";
    /**
     * Name of the spec currently loaded
     */
    public static final String I_SPEC_LOADED                = "specLoadedName";
    
    /** Resource persistent property for sticking the pcal call params */
    public static final String PCAL_CAL_PARAMS              = "pCalCallParams";
    /** Session property indicating if the resource has Pcal algorithm */
    public static final String CONTAINS_PCAL_ALGORITHM      = "hasPcalAlgorithm";
}
