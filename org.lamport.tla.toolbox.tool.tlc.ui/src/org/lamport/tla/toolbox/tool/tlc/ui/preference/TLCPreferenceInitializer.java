package org.lamport.tla.toolbox.tool.tlc.ui.preference;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;

/**
 * Class used to initialize default TLC preference values.
 */
public class TLCPreferenceInitializer extends AbstractPreferenceInitializer
{

    /**
     * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
     */
    public void initializeDefaultPreferences()
    {

        IPreferenceStore store = TLCUIActivator.getDefault().getPreferenceStore();
        store.setDefault(ITLCPreferenceConstants.I_TLC_POPUP_ERRORS, true);
        store.setDefault(ITLCPreferenceConstants.I_TLC_REVALIDATE_ON_MODIFY, true);
    }
}
