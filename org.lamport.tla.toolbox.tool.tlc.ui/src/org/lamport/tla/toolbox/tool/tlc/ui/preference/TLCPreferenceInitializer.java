package org.lamport.tla.toolbox.tool.tlc.ui.preference;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

import tlc2.TLCGlobals;

/**
 * Class used to initialize default TLC preference values.
 */
public class TLCPreferenceInitializer extends AbstractPreferenceInitializer
{

	public static final int MAX_HEAP_SIZE_DEFAULT = 25;

	/**
     * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
     */
    public void initializeDefaultPreferences()
    {

        IPreferenceStore store = TLCUIActivator.getDefault().getPreferenceStore();
        store.setDefault(ITLCPreferenceConstants.I_TLC_POPUP_ERRORS, true);
        store.setDefault(ITLCPreferenceConstants.I_TLC_REVALIDATE_ON_MODIFY, true);
        store.setDefault(ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT, MAX_HEAP_SIZE_DEFAULT);
        store.setDefault(ITLCPreferenceConstants.I_TLC_MAXSETSIZE_DEFAULT, TLCGlobals.setBound);
        store.setDefault(ITLCPreferenceConstants.I_TLC_AUTO_LOCK_MODEL_TIME,
                IModelConfigurationDefaults.MODEL_AUTO_LOCK_TIME_DEFAULT);
        // store.setDefault(ITLCPreferenceConstants.I_TLC_DELETE_PREVIOUS_FILES, true);
    }
}
