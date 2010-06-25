package org.lamport.tla.toolbox.util.pref;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.ui.preference.EditorPreferencePage;
import org.lamport.tla.toolbox.ui.preference.GeneralPreferencePage;

/**
 * Class used to initialize default preference values.
 */
public class PreferenceInitializer extends AbstractPreferenceInitializer
{

    /**
     * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
     */
    public void initializeDefaultPreferences()
    {

        IPreferenceStore store = PreferenceStoreHelper.getInstancePreferenceStore();
        store.setDefault(IPreferenceConstants.I_PARSER_POPUP_ERRORS, true); // set to true by LL on 22 Sep 2009

        // instance based properties
        store.setDefault(IPreferenceConstants.I_RESTORE_LAST_SPEC, true);
        store.setDefault(IPreferenceConstants.I_MIN_DISPLAYED_SIZE, GeneralPreferencePage.MIN_DISPLAYED_SIZE_DEFAULT);

        store.setDefault(IPreferenceConstants.I_PARSE_MODULE_ON_MODIFY, true);
        // store.setDefault(IPreferenceConstants.I_PARSE_FILES_ON_MODIFY, true);
        store.setDefault(IPreferenceConstants.I_PARSE_SPEC_ON_MODIFY, true);
        
        // set editor page preference defaults
        store.setDefault(EditorPreferencePage.EDITOR_RIGHT_MARGIN, 
                EditorPreferencePage.EDITOR_RIGHT_MARGIN_DEFAULT);
        
        store.setDefault(EditorPreferencePage.CLEAR_DECLARATION_USE_MARKERS_ON_PARSE, 
                EditorPreferencePage.CLEAR_DECLARATION_USE_MARKERS_ON_PARSE_DEFAULT);
    }

}
