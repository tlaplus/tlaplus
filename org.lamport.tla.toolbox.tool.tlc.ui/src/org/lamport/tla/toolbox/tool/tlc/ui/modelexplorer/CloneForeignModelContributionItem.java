package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;
import java.util.TreeSet;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.action.IContributionItem;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.actions.CompoundContributionItem;
import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.handlers.CloneModelHandlerDelegate;
import org.lamport.tla.toolbox.tool.tlc.launch.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Contributes a list of foreign models for cloning.
 */
public class CloneForeignModelContributionItem extends CompoundContributionItem {
    /**
     * Contrary to CloneModelHandlerDelegate.COMMAND_ID, no enabledWhen expression plugin.xml
     */
    public static final String COMMAND_ID_ALWAYS_ENABLED = CloneModelHandlerDelegate.COMMAND_ID + ".always.enabled";

    
    private final ImageDescriptor modelIcon = TLCUIActivator.getImageDescriptor("icons/full/choice_sc_obj.gif");

	protected IContributionItem[] getContributionItems() {
        final Spec currentSpec = ToolboxHandle.getCurrentSpec();
        if (currentSpec == null) {
        	return new IContributionItem[0];
        }
        
		final IProject specProject = currentSpec.getProject();
		final TreeMap<String, TreeSet<Model>> projectModelMap = new TreeMap<>();
		final Comparator<Model> c = (m1, m2) -> {
			return m1.getName().compareTo(m2.getName());
		};
		
		try {
			final IWorkspace iws = ResourcesPlugin.getWorkspace();
			final IWorkspaceRoot root = iws.getRoot();
			final IProject[] projects = root.getProjects();
			
			for (final IProject project : projects) {
				if (!specProject.equals(project)) {
					projectModelMap.put(project.getName(), new TreeSet<>(c));
				}
			}
			
			final String currentProjectName = specProject.getName();
			final ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
			final ILaunchConfigurationType launchConfigurationType
					= launchManager.getLaunchConfigurationType(TLCModelLaunchDelegate.LAUNCH_CONFIGURATION_TYPE);
			final ILaunchConfiguration[] launchConfigurations
					= launchManager.getLaunchConfigurations(launchConfigurationType);
			for (final ILaunchConfiguration launchConfiguration : launchConfigurations) {
				final String projectName = launchConfiguration.getAttribute(IConfigurationConstants.SPEC_NAME, "-l!D!q_-l!D!q_-l!D!q_");
				if (!projectName.equals(currentProjectName)) {
					final TreeSet<Model> models = projectModelMap.get(projectName);
					
					if (models != null) {
						final Model model = launchConfiguration.getAdapter(Model.class);
						
						if (!model.isSnapshot()) {
							models.add(model);
						}
					} else {
						TLCUIActivator.getDefault().logError("Could not generate model map for [" + projectName + "]!");
					}
				}
			}
		} catch (final CoreException e) {
			TLCUIActivator.getDefault().logError("Building foreign model map.", e);
			
			return null;
		}

        final ArrayList<IContributionItem> contributionItems = new ArrayList<>();
		for (final Map.Entry<String, TreeSet<Model>> me : projectModelMap.entrySet()) {
			final String specName = me.getKey();
			
			contributionItems.add(new Separator(specName));
			
			for (final Model model : me.getValue()) {
	            final String modelName = model.getName();

	            // provide required parameters to the handler (CloneModelHandlerDelegate)
	            final Map<String, String> parameters = new HashMap<String, String>();
	            parameters.put(CloneModelHandlerDelegate.PARAM_FOREIGN_FULLY_QUALIFIED_MODEL_NAME,
	            		model.getFullyQualifiedName());

	            CommandContributionItemParameter param
	            		= new CommandContributionItemParameter(  // get a load of this signature...
	            				UIHelper.getActiveWindow(),	// serviceLocator - workbench window or part site
	            				("toolbox.command.model.clone." + specName + "." + modelName),	// id for later reference
	            				COMMAND_ID_ALWAYS_ENABLED,	// the command id for the command attached to the item
	            				parameters,	// parameters to be used be the command
	            				modelIcon,	// icon for the item default / enabled
	            				null,		// icon for the item disabled
	            				null,		// icon for the item in hover
	            				(specName + " - " + modelName),  // the display text
	            				null,		// a mnemonic
	            				"Clones shit", //("Clones the foreign model, " + modelName + ", from the spec " + specName),	// the tooltip for the item
	            				CommandContributionItem.STYLE_PUSH,		// item's button style
	            				null,		// the help context id
	            				true);		// whether visibility tracking is enabled

	            contributionItems.add(new CommandContributionItem(param));
			}
		}

        return (IContributionItem[]) contributionItems.toArray(new IContributionItem[contributionItems.size()]);
    }
}
