package org.lamport.tla.toolbox.tool.tla2tex.preference;

/**
 * TLA2TeX preferences
 * 
 * @author Daniel Ricketts
 * @version $Id$
 */
public interface ITLA2TeXPreferenceConstants
{
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
}
