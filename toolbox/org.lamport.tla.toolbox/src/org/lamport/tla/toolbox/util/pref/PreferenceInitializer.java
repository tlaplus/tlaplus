package org.lamport.tla.toolbox.util.pref;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.ui.preference.EditorPreferencePage;
import org.lamport.tla.toolbox.ui.preference.GeneralPreferencePage;

/**
 * Class used to initialize default preference values.
 */
public class PreferenceInitializer extends AbstractPreferenceInitializer {
    /**
     * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
     */
	public void initializeDefaultPreferences() {
        final IPreferenceStore store = PreferenceStoreHelper.getInstancePreferenceStore();
        store.setDefault(IPreferenceConstants.I_PARSER_POPUP_ERRORS, true); // set to true by LL on 22 Sep 2009

        // instance based properties
        store.setDefault(IPreferenceConstants.I_RESTORE_LAST_SPEC, true);
        store.setDefault(IPreferenceConstants.I_MIN_DISPLAYED_SIZE, GeneralPreferencePage.MIN_DISPLAYED_SIZE_DEFAULT);

        store.setDefault(IPreferenceConstants.I_PARSE_MODULE_ON_MODIFY, true);
        // store.setDefault(IPreferenceConstants.I_PARSE_FILES_ON_MODIFY, true);
        store.setDefault(IPreferenceConstants.I_PARSE_SPEC_ON_MODIFY, true);
        
        /*
         * Set default (and only) option for PlusCal translator.  (Added by LL on 13 May 2016.)
         */
        store.setDefault(IPreferenceConstants.PCAL_CAL_PARAMS, "-nocfg"); 
        
        // set editor page preference defaults
        store.setDefault(EditorPreferencePage.EDITOR_RIGHT_MARGIN, 
                EditorPreferencePage.EDITOR_RIGHT_MARGIN_DEFAULT);
        
        store.setDefault(EditorPreferencePage.CLEAR_DECLARATION_USE_MARKERS_ON_PARSE, 
                EditorPreferencePage.CLEAR_DECLARATION_USE_MARKERS_ON_PARSE_DEFAULT);

        store.setDefault(EditorPreferencePage.EDITOR_ADD_MODIFICATION_HISTORY,
                EditorPreferencePage.EDITOR_ADD_MODIFICATION_HISTORY_DEFAULT);

        /*
         * Set default for Renumber Proof command option.
         */
        store.setDefault(EditorPreferencePage.RENUMBER_KEY,  
        		EditorPreferencePage.ALL_NAMES);
        store.setDefault(EditorPreferencePage.SAVE_MODULE, true);
        
        store.setDefault(IPreferenceConstants.I_FOLDING_BLOCK_COMMENTS, false);
        store.setDefault(IPreferenceConstants.I_FOLDING_PCAL_ALGORITHM, false);
        store.setDefault(IPreferenceConstants.I_FOLDING_PCAL_TRANSLATED, false);
    }
}
