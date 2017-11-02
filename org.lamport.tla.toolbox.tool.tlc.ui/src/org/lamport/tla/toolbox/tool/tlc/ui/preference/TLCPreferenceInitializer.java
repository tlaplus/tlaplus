package org.lamport.tla.toolbox.tool.tlc.ui.preference;

import org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.IScopeContext;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.internal.IPreferenceConstants;
import org.eclipse.ui.internal.WorkbenchPlugin;

import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.osgi.service.prefs.BackingStoreException;

import tlc2.TLCGlobals;
import tlc2.tool.fp.FPSetFactory;

/**
 * Class used to initialize default TLC preference values.
 */
@SuppressWarnings("restriction") // Discouraged access on the internal Eclipse classes referenced as part of Issue 101
public class TLCPreferenceInitializer extends AbstractPreferenceInitializer
{

	public static final int MAX_HEAP_SIZE_DEFAULT = 25;

	/**
     * @see org.eclipse.core.runtime.preferences.AbstractPreferenceInitializer#initializeDefaultPreferences()
     */
    public void initializeDefaultPreferences()
    {
        IPreferenceStore store = TLCUIActivator.getDefault().getPreferenceStore();
        
        store.setDefault(ITLCPreferenceConstants.I_TLC_TRACE_MAX_SHOW_ERRORS, 10000);
        store.setDefault(ITLCPreferenceConstants.I_TLC_POPUP_ERRORS, true);
        store.setDefault(ITLCPreferenceConstants.I_TLC_REVALIDATE_ON_MODIFY, true);
        store.setDefault(TLCActivator.I_TLC_SNAPSHOT_PREFERENCE, true);
        store.setDefault(ITLCPreferenceConstants.I_TLC_MAXIMUM_HEAP_SIZE_DEFAULT, MAX_HEAP_SIZE_DEFAULT);
        store.setDefault(ITLCPreferenceConstants.I_TLC_MAXSETSIZE_DEFAULT, TLCGlobals.setBound);
        store.setDefault(ITLCPreferenceConstants.I_TLC_FPBITS_DEFAULT, 1);
        store.setDefault(ITLCPreferenceConstants.I_TLC_FPSETIMPL_DEFAULT, FPSetFactory.getImplementationDefault());
        store.setDefault(ITLCPreferenceConstants.I_TLC_AUTO_LOCK_MODEL_TIME,
                         IModelConfigurationDefaults.MODEL_AUTO_LOCK_TIME_DEFAULT);
        
        // store.setDefault(ITLCPreferenceConstants.I_TLC_DELETE_PREVIOUS_FILES, true);
        
        if (! store.contains(ITLCPreferenceConstants.I_TLC_ISSUE_101)) {
            IScopeContext context = InstanceScope.INSTANCE;
            IEclipsePreferences node = context.getNode(WorkbenchPlugin.getDefault().getBundle().getSymbolicName());

            node.putBoolean(IPreferenceConstants.RUN_IN_BACKGROUND, false);
            try {
                node.flush();
            }
            catch (BackingStoreException e) {
                TLCUIActivator.getDefault().logError("Error trying to flush the workbench plugin preferences store.", e);
            }
            
            store.setValue(ITLCPreferenceConstants.I_TLC_ISSUE_101, true);
        }
    }
    
}
