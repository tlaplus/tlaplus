package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.Vector;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.ui.IEditorPart;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Deletes the launch configuration
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DeleteModelHandler extends AbstractHandler implements IModelConfigurationConstants
{
    public static final String PARAM_MODEL_NAME = "toolbox.tool.tlc.commands.model.delete.param";
    public static final String COMMAND_ID = "toolbox.tool.tlc.commands.model.delete";

    /**
     * The constructor.
     */
    public DeleteModelHandler()
    {
    }

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // get the launch manager
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();

        // get the launch type (model check)
        ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);

        String modelName = event.getParameter(DeleteModelHandler.PARAM_MODEL_NAME);
        if (modelName == null)
        {
            System.out.println("Leaving delete model handler. No model name specified.");
            return null;
        }
        System.out.println("Delete model '" + modelName + "'");

        Vector couldNotDelete = new Vector();
        try
        {
            ILaunchConfiguration[] launchConfigurations = launchManager
                    .getLaunchConfigurations(launchConfigurationType);
            for (int i = 0; i < launchConfigurations.length; i++)
            {
                // find the corresponding model
                if (modelName.equals(ModelHelper.getModelName(launchConfigurations[i].getFile())))
                {
                    if (ModelHelper.isModelLocked(launchConfigurations[i]))
                    {
                        couldNotDelete.add(launchConfigurations[i]);
                    } else
                    {
                        // if the editor is opened
                        IEditorPart editorWithModelOpened = ModelHelper.getEditorWithModelOpened(launchConfigurations[i]);
                        if (editorWithModelOpened != null) 
                        {
                            // close it
                            UIHelper.getActivePage().closeEditor(editorWithModelOpened, false);
                        }
                        launchConfigurations[i].delete();
                    }
                }
            }
            // some elements could not be deleted
            if (couldNotDelete.size() > 0)
            {
                MessageDialog.openError(UIHelper.getShellProvider().getShell(), "Could not delete a model",
                        "Could not delete the model " + modelName + ", because it is being model checked.");
            }
        } catch (CoreException e)
        {
            e.printStackTrace();
        }
        return null;
    }

}
