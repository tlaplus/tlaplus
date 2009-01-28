package org.lamport.tla.toolbox.util.pref;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;

/**
 * Class used to initialize default preference values.
 */
public class PreferenceInitializer extends AbstractPreferenceInitializer {

	/**
	 * 
	 * 
	 * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
	 */
	public void initializeDefaultPreferences() {
		
	    IPreferenceStore store = PreferenceStoreHelper.getInstancePreferenceStore();
		store.setDefault(IPreferenceConstants.P_PARSER_POPUP_ERRORS, false);
		store.setDefault(IPreferenceConstants.I_RESTORE_LAST_SPEC, true);
	}

}
