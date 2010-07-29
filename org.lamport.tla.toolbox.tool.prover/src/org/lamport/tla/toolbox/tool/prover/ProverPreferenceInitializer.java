package org.lamport.tla.toolbox.tool.prover;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.tool.prover.ui.ProverUIActivator;
import org.lamport.tla.toolbox.tool.prover.ui.dialog.LaunchProverDialog;

/**
 * This class can be used to set default preferences for any preference
 * values that are stored in the preference store for this plugin. This
 * preference store is the one returned by ProverUIActivator.getDefault().getPreferenceStore().
 * 
 * @author Daniel Ricketts
 *
 */
public class ProverPreferenceInitializer extends AbstractPreferenceInitializer
{

    public void initializeDefaultPreferences()
    {
        IPreferenceStore store = ProverUIActivator.getDefault().getPreferenceStore();

        /*
         * Set the default values for the general prover launching
         * dialog.
         */
        store.setDefault(LaunchProverDialog.TOOLBOX_MODE_KEY, true);
        store.setDefault(LaunchProverDialog.EXTRA_OPTIONS_KEY, "");
        store.setDefault(LaunchProverDialog.NUM_THREADS_KEY, 1);
        store.setDefault(LaunchProverDialog.PARANOID_KEY, false);
        store.setDefault(LaunchProverDialog.STATUS_CHECK_KEY, false);
    }

}
