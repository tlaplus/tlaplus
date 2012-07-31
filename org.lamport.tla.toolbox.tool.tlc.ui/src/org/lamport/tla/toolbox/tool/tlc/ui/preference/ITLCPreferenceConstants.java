package org.lamport.tla.toolbox.tool.tlc.ui.preference;

import tlc2.tool.fp.FPSet;

/**
 * TLC preferences
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface ITLCPreferenceConstants
{
    /** 
     * Popup on TLC errors
     */
    public static final String I_TLC_POPUP_ERRORS = "popupOnMCErrors";
    /**
     * Re-validate model on save
     */
    public static final String I_TLC_REVALIDATE_ON_MODIFY = "revalidateOnModify";
    // /**
    // * Delete data (.st files and unused checkpoints) from the previous run)
    // */
    // public static final String I_TLC_DELETE_PREVIOUS_FILES = "deleteUnusedMCData";
    public static final String I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT = "maxHeapSizeDefault";

    public static final String I_TLC_FPBITS_DEFAULT = "fpBitsDefault";
    
    public static final String I_TLC_MAXSETSIZE_DEFAULT = "maxSetSizeDefault";
    /**
     * Automatically lock model after TLC exceeds given length of time.
     */
    public static final String I_TLC_AUTO_LOCK_MODEL_TIME = "autoLockModelTime";
    /**
     * font used for text in the error viewer at the top of the TLC error
     * view, the User Output field on the results page, and the Progress
     * Output on the results page.
     * 
     * Note: this preference appears in the preference page General > Appearance > Colors and Fonts
     * It is put there by registering an extension to the extension point org.eclipse.ui.themes
     */
    public static final String I_TLC_OUTPUT_FONT = "org.lamport.tla.toolbox.tool.tlc.ui.tlcOutputFont";
	/**
	 * Implementation of {@link FPSet} to use during model checking
	 */
	public static final String I_TLC_FPSETIMPL_DEFAULT = "fpSetImpl";

}
