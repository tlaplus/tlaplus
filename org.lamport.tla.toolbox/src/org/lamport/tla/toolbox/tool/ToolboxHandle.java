package org.lamport.tla.toolbox.tool;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * Provides shortcuts to the internal toolbox methods, that should be made accessible to the other tools
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ToolboxHandle
{
    public static String I_RESTORE_LAST_SPEC = IPreferenceConstants.I_RESTORE_LAST_SPEC;
    
    
    /**
     * Retrieves the root file of the loaded spec or <code>null</code> if no spec selected
     */
    public static IFile getRootModule()
    {
        return ((Activator.getSpecManager().getSpecLoaded() == null) ? null : Activator.getSpecManager().getSpecLoaded().getRootFile()); 
    }
    
    /**
     * Returns the instance preference store
     */
    public static IPreferenceStore getInstanceStore()
    {
        return PreferenceStoreHelper.getInstancePreferenceStore();
    }
}
