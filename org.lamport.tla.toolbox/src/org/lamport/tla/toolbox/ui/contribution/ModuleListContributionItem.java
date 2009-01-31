package org.lamport.tla.toolbox.ui.contribution;

import java.util.HashMap;
import java.util.Vector;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.action.IContributionItem;
import org.eclipse.jface.action.Separator;
import org.eclipse.ui.actions.CompoundContributionItem;
import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.handler.AddModuleHandler;
import org.lamport.tla.toolbox.ui.handler.OpenModuleHandler;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Contribution item for opening the modules
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModuleListContributionItem extends CompoundContributionItem
{
    /**
     * @see org.eclipse.ui.actions.CompoundContributionItem#getContributionItems()
     */
    protected IContributionItem[] getContributionItems()
    {

        Spec spec = Activator.getSpecManager().getSpecLoaded();
        Vector moduleContributions = new Vector();
        HashMap parameters = new HashMap();

        // create the contribution item for open with
        CommandContributionItemParameter param = new CommandContributionItemParameter(UIHelper.getActiveWindow(),
                "toolbox.command.module.add", AddModuleHandler.COMMAND_ID, parameters, null, null, null,
                "Add TLA+ Module...", null, "Adds new TLA+ Module to the specification",
                CommandContributionItem.STYLE_PUSH, null, true);

        // add contribution item to the list
        moduleContributions.add(new CommandContributionItem(param));
        moduleContributions.add(new Separator());

        if (spec != null)
        {
            IResource[] members = spec.getModules();
            for (int i = 0; i < members.length; i++)
            {
                if (!ResourceHelper.isModule(members[i]))
                {
                    continue;
                }

                parameters = new HashMap();
                // fill the module name for the handler
                parameters.put(OpenModuleHandler.PARAM_MODULE, ResourceHelper.getModuleNameChecked(
                        members[i].getName(), false));

                // create the contribution item
                param = new CommandContributionItemParameter(UIHelper.getActiveWindow(), "toolbox.command.module.open."
                        + members[i].getName(), OpenModuleHandler.COMMAND_ID, parameters, null, null, null, members[i]
                        .getName(), null, "Opens " + members[i].getName(), CommandContributionItem.STYLE_PUSH, null,
                        true);

                // add contribution item to the list
                moduleContributions.add(new CommandContributionItem(param));
            }
        }

        return (IContributionItem[]) moduleContributions.toArray(new IContributionItem[moduleContributions.size()]);
    }

}
