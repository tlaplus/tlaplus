package org.lamport.tla.toolbox.tool.tlc.ui.preference;

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
    /**
     * Automatically lock model after TLC exceeds given length of time.
     */
    public static final String I_TLC_AUTO_LOCK_MODEL_TIME = "autoLockModelTime";

}
