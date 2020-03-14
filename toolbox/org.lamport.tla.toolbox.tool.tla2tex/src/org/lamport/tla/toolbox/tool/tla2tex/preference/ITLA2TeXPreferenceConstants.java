package org.lamport.tla.toolbox.tool.tla2tex.preference;

/**
 * TLA2TeX preferences
 * 
 * @author Daniel Ricketts
 */
public interface ITLA2TeXPreferenceConstants
{
    /**
     * Automatically regenerate the pretty-printed PDF when the
     * corresponding spec is saved.
     */
    public static final String AUTO_REGENERATE = "autoRegenerateOnSave";
    
    /**
     * Shade comments in tla2tex output file
     */
    public static final String SHADE_COMMENTS = "shadeComments";

    /**
     * Do not shade PlusCal algorithm in tla2tex output file
     */
    public static final String NO_PCAL_SHADE = "noPcalShade";

    /**
     * Number lines in tla2tex output file
     */
    public static final String NUMBER_LINES = "numberLines";

    /**
     * Specify latex command to be used
     */
    public static final String LATEX_COMMAND = "latexCommand";

    /**
     * Specify grey level
     */
    public static final String GRAY_LEVEL = "greyLevel";

    /**
     * True if embedded viewer is to be used
     */
    public static final String EMBEDDED_VIEWER = "embeddedViewer";

    /**
     * True if the operating system should open the PDF - currently only used on macOS
     */
    public static final String HAVE_OS_OPEN_PDF = "osHandlesPDF";

	/**
	 * Specify the full qualified path to GraphViz's dot executable.
	 */
	public static final String DOT_COMMAND = "dotCommand";
}
