package org.lamport.tla.toolbox.tool;

import java.io.File;
import java.io.IOException;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.preference.IPreferenceStore;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

import tla2sany.modanalyzer.SpecObj;

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
     * Retrieves the filename of the config file
     * TODO HACK 
     */
    public static String getConfigFilename()
    {
        IFile rootModule = getRootModule();

        String cfgPath = rootModule.getLocation().removeFileExtension().addFileExtension("cfg").toOSString();
        
        File cfgFile = new File(cfgPath);
        if (!cfgFile.exists())
        {
            try
            {
                cfgFile.createNewFile();
            } catch (IOException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        if (cfgFile != null && cfgFile.exists())
        {
            return cfgFile.getName();
        } else {
            return null;
        }
        
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
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec != null) 
        {
            return spec.getValidRootModule();
        }
        return null;
    }
    
    
}
