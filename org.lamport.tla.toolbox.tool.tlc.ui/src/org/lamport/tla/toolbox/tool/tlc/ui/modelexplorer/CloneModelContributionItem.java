package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

import java.util.HashMap;
import java.util.Vector;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.action.IContributionItem;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.actions.CompoundContributionItem;
import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.handlers.CloneModelHandlerDelegate;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Contributes a list of models for cloning.
 * 
 * @author Daniel Ricketts
 *
 */
public class CloneModelContributionItem extends CompoundContributionItem
{

    private ImageDescriptor modelIcon = TLCUIActivator.getImageDescriptor("icons/full/choice_sc_obj.gif");

    protected IContributionItem[] getContributionItems()
    {
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);

        Vector modelContributions = new Vector();

        IProject specProject = ToolboxHandle.getCurrentSpec().getProject();

        try
        {
            // refresh local to pick up any models that have been added
            // to the file system but not recognized by the toolbox's resource
            // framework.
            specProject.refreshLocal(IResource.DEPTH_ONE, new NullProgressMonitor());

            // First, search for all models for the given spec.
            ILaunchConfiguration[] launchConfigurations = launchManager
                    .getLaunchConfigurations(launchConfigurationType);
            for (int i = 0; i < launchConfigurations.length; i++)
            {
                String modelName = launchConfigurations[i].getName();

                // skip launches from other specs
                if (!specProject.equals(launchConfigurations[i].getFile().getProject()))
                {
                    continue;
                }

                // Next, set the command and the parameters for the command
                // that will be called when the user selects this item.
                HashMap parameters = new HashMap();

                // user visible model name
                String modelNameUser = ModelHelper.getModelName(launchConfigurations[i].getFile());

                // fill the model name for the handler
                parameters.put(CloneModelHandlerDelegate.PARAM_MODEL_NAME, modelNameUser);

                // create the contribution item
                CommandContributionItemParameter param = new CommandContributionItemParameter(UIHelper
                        .getActiveWindow(), "toolbox.command.model.clone." + modelName,
                        CloneModelHandlerDelegate.COMMAND_ID, parameters, modelIcon, null, null, modelNameUser, null,
                        "Clones " + modelNameUser, CommandContributionItem.STYLE_PUSH, null, true);

                // add contribution item to the list
                modelContributions.add(new CommandContributionItem(param));
            }

        } catch (CoreException e)
        {

        }
        return (IContributionItem[]) modelContributions.toArray(new IContributionItem[modelContributions.size()]);
    }

}
