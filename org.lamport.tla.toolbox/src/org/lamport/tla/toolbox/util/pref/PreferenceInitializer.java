package org.lamport.tla.toolbox.util.pref;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;

/**
 * Class used to initialize default preference values.
 */
public class PreferenceInitializer extends AbstractPreferenceInitializer {

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
	 */
	public void initializeDefaultPreferences() {
		
	    IPreferenceStore store = PreferenceStoreHelper.getInstancePreferenceStore();
		store.setDefault(IPreferenceConstants.P_PARSER_RUN_ON_MODIFICATION, true);
		store.setDefault(IPreferenceConstants.P_PARSER_POPUP_ERRORS, false);
		
		/*
		store.setDefault(IPreferenceConstants.P_CHOICE, "choice2");
		store.setDefault(IPreferenceConstants.P_STRING, "Default value");
		*/
	}

}
