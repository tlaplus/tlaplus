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
}
