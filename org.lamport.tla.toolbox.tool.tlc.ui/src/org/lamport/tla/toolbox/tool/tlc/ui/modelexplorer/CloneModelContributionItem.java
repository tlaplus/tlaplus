package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

import java.util.HashMap;
import java.util.Map;
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
import org.lamport.tla.toolbox.spec.Spec;
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
    /**
     * Contrary to CloneModelHandlerDelegate.COMMAND_ID, no enabledWhen expression plugin.xml
     */
    public static final String COMMAND_ID_ALWAYS_ENABLED = CloneModelHandlerDelegate.COMMAND_ID + ".always.enabled";

    private ImageDescriptor modelIcon = TLCUIActivator.getImageDescriptor("icons/full/choice_sc_obj.gif");

    protected IContributionItem[] getContributionItems()
    {
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        ILaunchConfigurationType launchConfigurationType = launchManager
                .getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);

        final Vector<CommandContributionItem> modelContributions = new Vector<CommandContributionItem>();

        Spec currentSpec = ToolboxHandle.getCurrentSpec();
        if (currentSpec == null) {
        	return new IContributionItem[0];
        }
		IProject specProject = currentSpec.getProject();

        try
        {
            // refresh local to pick up any models that have been added
            // to the file system but not recognized by the toolbox's resource
            // framework.
			// TODO decouple from UI thread or question why it has to be done
			// here. Meaning, why doesn't the resource fw handle this case
			// already?
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
                Map<String, String> parameters = new HashMap<String, String>();

                // user visible model name
                String modelNameUser = ModelHelper.getModelName(launchConfigurations[i].getFile());

                // fill the model name for the handler
                parameters.put(CloneModelHandlerDelegate.PARAM_MODEL_NAME, modelNameUser);

                // create the contribution item
                CommandContributionItemParameter param = new CommandContributionItemParameter(UIHelper
                        .getActiveWindow(), "toolbox.command.model.clone." + modelName,
                        COMMAND_ID_ALWAYS_ENABLED, parameters, modelIcon, null, null, modelNameUser, null,
                        "Clones " + modelNameUser, CommandContributionItem.STYLE_PUSH, null, true);

                // add contribution item to the list
                modelContributions.add(new CommandContributionItem(param));
            }

        } catch (CoreException e)
        {
        	e.printStackTrace();
        }
        return (IContributionItem[]) modelContributions.toArray(new IContributionItem[modelContributions.size()]);
    }
}
