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
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.job.ConfigCreationOperation;
import org.lamport.tla.toolbox.tool.tlc.job.ExtendingTLAModuleCreationOperation;
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
     * 
     * This method tests the existence of the launch configuration AND of the file
     * 
     * @param specProject
     * @param specName
     * @return
     */
    public static String constructModelName(IProject specProject, String specName)
    {
        return doConstructModelName(specProject, specName + "_MC_1");
    }
    
    /**
     * Implementation of the {@link ModelHelper#constructModelName(IProject, String)}
     * @param specProject
     * @param proposition
     * @return
     */
    private static String doConstructModelName(IProject specProject, String proposition)
    {
        ILaunchConfiguration existingModel = getModelByName(specProject, proposition);
        if (existingModel != null || specProject.getFile(proposition + ".tla").exists())
        {
            String oldNumber = proposition.substring(proposition.lastIndexOf("_") + 1);
            int number = Integer.parseInt(oldNumber) + 1;
            proposition = proposition.substring(0, proposition.lastIndexOf("_") + 1);
            return doConstructModelName(specProject, proposition + number);
        }

        return proposition;
    }

    /**
     * Convenience method retrieving the model for the project of the current specification
     * @param modelName name of the model
     * @return launch configuration or null, if not found
     */
    public static ILaunchConfiguration getModelByName(String modelName)
    {
        return getModelByName(ToolboxHandle.getCurrentSpec().getProject(), modelName);
    }

    /**
     * @param specProject
     * @param modelName
     * @return
     */
    public static ILaunchConfiguration getModelByName(IProject specProject, String modelName)
    {
        //TODO! add project test
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        ILaunchConfigurationType launchConfigurationType = launchManager
        .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_ID);

        try
        {
            ILaunchConfiguration[] launchConfigurations = launchManager.getLaunchConfigurations(launchConfigurationType);
            for (int i = 0; i < launchConfigurations.length; i++)
            {
                
                if (launchConfigurations[i].getName().equals(modelName)) 
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
     * Convenience method
     * @param modelFile file containing the model
     * @return ILaunchconfiguration
     */
    public static ILaunchConfiguration getModelByFile(IFile modelFile)
    {
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        return launchManager.getLaunchConfiguration(modelFile);
    }

    
    /**
     * Retrieves the the config file
     * REFACTOR HACK 
     */
    public static IFile getConfigFile(IResource rootModule)
    {
        
        IPath cfgPath = rootModule.getLocation().removeFileExtension().addFileExtension("cfg");

        
        // create config file
        IWorkspaceRunnable configCreateJob = new ConfigCreationOperation(cfgPath);
        // create it
        try
        {
            ResourcesPlugin.getWorkspace().run(configCreateJob, null);
        } catch (CoreException e)
        {
            e.printStackTrace();
            // exception, no chance to recover
        }
        
        
        IFile cfgFile = ResourceHelper.getLinkedFile(rootModule.getProject(), cfgPath.toOSString(), true);

        return cfgFile;
    }
    
    /**
     * Creates a new model root and retrieves the handle to it
     */
    public static IFile getNewModelRootFile(IResource specRootModule, String modelName)
    {
        // construct new model checking root module name
        IPath modelRootPath = specRootModule.getLocation().removeLastSegments(1).append(modelName + ".tla");

        
        // create a module
        IWorkspaceRunnable moduleCreateJob = new ExtendingTLAModuleCreationOperation(modelRootPath, ResourceHelper.getModuleName(specRootModule));
        // create it
        try
        {
            ResourcesPlugin.getWorkspace().run(moduleCreateJob, null);
        } catch (CoreException e)
        {
            e.printStackTrace();
            // exception, no chance to recover
        }

        
        // create a link in the project
        IFile modelRootFile = ResourceHelper.getLinkedFile(specRootModule.getProject(), modelRootPath.toOSString(), true);

        return modelRootFile;
    }
    
    /**
     * Saves the config working copy
     * @param config
     */
    public static void doSaveConfigurationCopy(ILaunchConfigurationWorkingCopy config)
    {
        try
        {
            config.doSave();
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
}
