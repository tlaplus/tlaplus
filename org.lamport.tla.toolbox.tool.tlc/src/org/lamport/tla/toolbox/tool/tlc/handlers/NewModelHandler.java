package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Our sample handler extends AbstractHandler, an IHandler base class.
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class NewModelHandler extends AbstractHandler implements IConfigurationConstants
{
    public static final Object PARAM_MODEL_NAME = "modelLaunchName";
    /**
     * The constructor.
     */
    public NewModelHandler()
    {
    }

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // root file
        IResource specRootModule = ToolboxHandle.getRootModule();

        // get the launch manager
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        
        // get the launch type (model check)
        ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_ID);

        // retrieve a new model name for the spec 
        String modelName = ModelHelper.constructModelName(specRootModule.getProject(), ToolboxHandle.getCurrentSpec()
                .getName());
        
        // get the model root file
        IResource modelRoot = ModelHelper.getNewModelRootFile(specRootModule, modelName);
        
        // get the model configuration
        IResource config = ModelHelper.getConfigFile(modelRoot);
        

        try
        {

            // create new launch instance
            ILaunchConfigurationWorkingCopy launchCopy = launchConfigurationType.newInstance(specRootModule.getProject(),
                    modelName);

            launchCopy.setAttribute(SPEC_NAME, ToolboxHandle.getCurrentSpec().getName());
            launchCopy.setAttribute(SPEC_ROOT_FILE, ToolboxHandle.getRootModule().getLocation().toOSString());
            launchCopy.setAttribute(MODEL_NAME, modelName);
            launchCopy.setAttribute(MODEL_ROOT_FILE, modelRoot.getLocation().toOSString());
            launchCopy.setAttribute(CONFIG_FILE, config.getLocation().toOSString());

            ILaunchConfiguration launchSaved = launchCopy.doSave();

            return launchSaved;
            
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        return null;
    }
}
