package org.lamport.tla.toolbox.tool.tlc.ui.preference;

import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;

import tlc2.tool.fp.FPSet;

/**
 * TLC preferences
 * @author Simon Zambrovski
 */
public interface ITLCPreferenceConstants {
    /** 
     * TODO this is not TLC - this is model editor
     * 
     * Popup on TLC errors
     */
    public static final String I_TLC_POPUP_ERRORS = "popupOnMCErrors";
    /**
     * TODO this is not TLC - this is model editor
     * 
     * Re-validate model on save
     */
    public static final String I_TLC_REVALIDATE_ON_MODIFY = "revalidateOnModify";
    /**
     * TODO this is not TLC - this is model editor
     * 
	 * Font used for text in the error viewer at the top of the TLC error view, the
	 * User Output field on the results page, and the Progress Output on the results
	 * page.
	 * 
	 * Note: this preference appears in the preference page General > Appearance >
	 * Colors and Fonts It is put there by registering an extension to the extension
	 * point org.eclipse.ui.themes
	 */
    public static final String I_TLC_OUTPUT_FONT = "org.lamport.tla.toolbox.tool.tlc.ui.tlcOutputFont";
    /**
     * TODO this is not TLC - this is model editor
     * 
	 * Font used for text in the error trace viewer in the TLC error view.
	 * 
	 * Note: this preference appears in the preference page General > Appearance >
	 * Colors and Fonts It is put there by registering an extension to the extension
	 * point org.eclipse.ui.themes
	 */
    public static final String I_TLC_ERROR_TRACE_FONT = "org.lamport.tla.toolbox.tool.tlc.ui.tlcErrorTraceFont";
	/**
     * TODO this is not TLC - this is model editor
     * 
	 * If set, the Toolbox will open a modal progress dialog to indicate TLC
	 * startup. A user can opt to subsequently suppress the dialog. This returns the
	 * old behavior prior to the change in https://bugs.eclipse.org/146205#c10.
	 */
	public static final String I_TLC_SHOW_MODAL_PROGRESS = "showModalProgress";
    // /**
    // * Delete data (.st files and unused checkpoints) from the previous run)
    // */
    // public static final String I_TLC_DELETE_PREVIOUS_FILES = "deleteUnusedMCData";
    
    
    /** 
     * Maximum number of states to show in {@link TLCErrorView}
     */
    public static final String I_TLC_TRACE_MAX_SHOW_ERRORS = "traceMaxShowErrors";

    public static final String I_TLC_DEFAULT_WORKERS_COUNT = "tlcWorkersCountDefault";
    
    public static final String I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT = "maxHeapSizeDefault";

    public static final String I_TLC_FPBITS_DEFAULT = "fpBitsDefault";
    
    public static final String I_TLC_MAXSETSIZE_DEFAULT = "maxSetSizeDefault";

	/**
	 * Implementation of {@link FPSet} to use during model checking
	 */
	public static final String I_TLC_FPSETIMPL_DEFAULT = "fpSetImpl";
}
