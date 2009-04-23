package org.lamport.tla.toolbox.tool;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

import tla2sany.modanalyzer.SpecObj;
import util.UniqueString;

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
    
    /**
     * Returns the SpecObj of the current loaded specification
     * @return SpecObj produced by the previous SANY run, or null
     */
    public static SpecObj getSpecObj()
    {
        Spec spec = null;
        try 
        {
            spec = Activator.getSpecManager().getSpecLoaded();
        } catch (IllegalStateException e) 
        {
            // this happens is the workspace is closed
            // just return null for e.G. JUnit tests
        }
        if (spec != null) 
        {
            return spec.getValidRootModule();
        }
        return null;
    }


    /**
     * @return
     */
    public static Spec getCurrentSpec()
    {
        return Activator.getSpecManager().getSpecLoaded();
    }

    /**
     * @param name
     * @return
     */
    public static boolean isUserModule(String name)
    {
        if (name == null || name.isEmpty()) 
        {
            return false;
        }
        return Activator.getModuleDependencyStorage().hasModule(name);
    }
    
    
}
