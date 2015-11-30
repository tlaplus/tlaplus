package org.lamport.tla.toolbox.tool.tlc.ui.modelexplorer;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import org.eclipse.jface.action.IContributionItem;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.actions.CompoundContributionItem;
import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.handlers.OpenModelHandler;
import org.lamport.tla.toolbox.tool.tlc.model.TLCSpec;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Contributes a list of models
 * @author Simon Zambrovski
 */
public class ModelContributionItem extends CompoundContributionItem
{
    private ImageDescriptor modelIcon = TLCUIActivator.getImageDescriptor("icons/full/choice_sc_obj.gif");

    /**
     * @see org.eclipse.ui.actions.CompoundContributionItem#getContributionItems()
     */
    protected IContributionItem[] getContributionItems()
    {
        final Vector<CommandContributionItem> modelContributions = new Vector<CommandContributionItem>();

        Spec currentSpec = ToolboxHandle.getCurrentSpec();
        if (currentSpec == null) {
        	return new IContributionItem[0];
        }
		// First, search for all models for the given spec.
		final Set<String> modelNames = currentSpec.getAdapter(TLCSpec.class).getModels().keySet();
		for (String modelName : modelNames) {

            Map<String, String> parameters = new HashMap<String, String>();

            // fill the model name for the handler
            parameters.put(OpenModelHandler.PARAM_MODEL_NAME, modelName);

            // create the contribution item
            CommandContributionItemParameter param = new CommandContributionItemParameter(UIHelper
                    .getActiveWindow(), "toolbox.command.model.open." + modelName, OpenModelHandler.COMMAND_ID,
                    parameters, modelIcon, null, null, modelName, null, "Opens " + modelName,
                    CommandContributionItem.STYLE_PUSH, null, true);

            // add contribution item to the list
            modelContributions.add(new CommandContributionItem(param));
        }
        return modelContributions.toArray(new IContributionItem[modelContributions.size()]);
    }

}
