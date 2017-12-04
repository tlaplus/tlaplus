package org.lamport.tla.toolbox.tool.tlc.ui.preference;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.internal.IPreferenceConstants;
import org.eclipse.ui.internal.WorkbenchPlugin;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.osgi.service.prefs.BackingStoreException;

import tlc2.TLCGlobals;
import tlc2.tool.fp.FPSetFactory;

/**
 * Class used to initialize default TLC preference values.
 */
@SuppressWarnings("restriction")
public class TLCPreferenceInitializer extends AbstractPreferenceInitializer
{

	public static final int MAX_HEAP_SIZE_DEFAULT = 25;

	/**
     * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
     */
    public void initializeDefaultPreferences()
    {
        final IPreferenceStore uiPreferencesStore = TLCUIActivator.getDefault().getPreferenceStore();
        final IPreferenceStore tlcPreferencesStore = TLCActivator.getDefault().getPreferenceStore();

        tlcPreferencesStore.setDefault(TLCActivator.I_TLC_SNAPSHOT_KEEP_COUNT, 10);

        // This is so bad.. we store them in parallel because one is needed by plugin relied upon the PreferencePage
        //      and the other by a plugin which is on the opposite side of the dependency. (TLCModelLaunchDelegate)
        uiPreferencesStore.setDefault(TLCActivator.I_TLC_SNAPSHOT_KEEP_COUNT, 10);

        uiPreferencesStore.setDefault(ITLCPreferenceConstants.I_TLC_TRACE_MAX_SHOW_ERRORS, 10000);
        uiPreferencesStore.setDefault(ITLCPreferenceConstants.I_TLC_POPUP_ERRORS, true);
        uiPreferencesStore.setDefault(ITLCPreferenceConstants.I_TLC_REVALIDATE_ON_MODIFY, true);
        uiPreferencesStore.setDefault(ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT, MAX_HEAP_SIZE_DEFAULT);
        uiPreferencesStore.setDefault(ITLCPreferenceConstants.I_TLC_MAXSETSIZE_DEFAULT, TLCGlobals.setBound);
        uiPreferencesStore.setDefault(ITLCPreferenceConstants.I_TLC_FPBITS_DEFAULT, 1);
        uiPreferencesStore.setDefault(ITLCPreferenceConstants.I_TLC_FPSETIMPL_DEFAULT, FPSetFactory.getImplementationDefault());
        // store.setDefault(ITLCPreferenceConstants.I_TLC_DELETE_PREVIOUS_FILES, true);

		// By default we want the Toolbox to show a modal progress dialog upon TLC
		// startup. A user can opt to subsequently suppress the dialog.
		// This restores the behavior prior to https://bugs.eclipse.org/146205#c10.
        if (!uiPreferencesStore.contains(ITLCPreferenceConstants.I_TLC_SHOW_MODAL_PROGRESS)) {
			final IEclipsePreferences node = InstanceScope.INSTANCE
					.getNode(WorkbenchPlugin.getDefault().getBundle().getSymbolicName());
			node.putBoolean(IPreferenceConstants.RUN_IN_BACKGROUND, false);
			try {
				node.flush();
			} catch (final BackingStoreException e) {
				TLCUIActivator.getDefault().logError("Error trying to flush the workbench plugin preferences store.",
						e);
			}
			uiPreferencesStore.setValue(ITLCPreferenceConstants.I_TLC_SHOW_MODAL_PROGRESS, true);
		}
    }
}
