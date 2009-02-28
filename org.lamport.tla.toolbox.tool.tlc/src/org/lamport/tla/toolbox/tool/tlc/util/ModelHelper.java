package org.lamport.tla.toolbox.tool.tlc.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Provides utility methods for model manipulation
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelHelper
{

    /**
     * Constructs the model called FOO_MC_1 from the SpecName FOO
     * if FOO_MC_1 already exists, delivers FOO_MC_2, and so on...
     * @param specProject
     * @param specName
     * @return
     */
    public static String constructModelName(IProject specProject, String specName)
    {
        return constructModelNameName(specProject, specName + "_MC_1");
    }
    
    
    private static String constructModelNameName(IProject specProject, String proposition)
    {
        ILaunchConfiguration existingModel = getModelByName(specProject, proposition);
        if (existingModel != null)
        {
            String oldNumber = proposition.substring(proposition.lastIndexOf("_") + 1);
            int number = Integer.parseInt(oldNumber) + 1;
            proposition = proposition.substring(0, proposition.lastIndexOf("_") + 1);
            return constructModelNameName(specProject, proposition + number);
        }

        return proposition;
    }


    /**
     * TODO! add project test
     * @param specProject
     * @param proposition
     * @return
     */
    public static ILaunchConfiguration getModelByName(IProject specProject, String proposition)
    {
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        ILaunchConfigurationType launchConfigurationType = launchManager
        .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_ID);

        try
        {
            ILaunchConfiguration[] launchConfigurations = launchManager.getLaunchConfigurations(launchConfigurationType);
            for (int i = 0; i < launchConfigurations.length; i++)
            {
                
                if (launchConfigurations[i].getName().equals(proposition)) 
                {
                    return launchConfigurations[i];
                }
            }
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        return null;
    }

    
    /**
     * Retrieves the the config file
     * REFACTOR HACK 
     */
    public static IFile getConfigFile(IResource rootModule)
    {
        
        IPath cfgPath = rootModule.getLocation().removeFileExtension().addFileExtension("cfg");

        
        
        IFile cfgFile = ResourceHelper.getLinkedFile(rootModule.getProject(), cfgPath.toOSString(), true);

        return cfgFile;
    }
    
    /**
     * Creates a new model check root
     */
    public static IFile getModelRootFile(IResource specRootModule, String modelName)
    {
        // construct new model checking root module name
        IPath modelRootPath = specRootModule.getLocation().removeLastSegments(1).append(modelName + ".tla");

        
        // create a module
        IWorkspaceRunnable moduleCreateOperation = ResourceHelper.createTLAModuleCreationOperation(modelRootPath);

        try
        {
            ResourcesPlugin.getWorkspace().run(moduleCreateOperation, null);
        } catch (CoreException e)
        {
            e.printStackTrace();
            // exception, no chance to recover
            return null;
        }
        
        // create a link in the project
        IFile modelRootFile = ResourceHelper.getLinkedFile(specRootModule.getProject(), modelRootPath.toOSString(), true);

        return modelRootFile;
    }


}
