package org.lamport.tla.toolbox.ui.contribution;

import java.util.HashMap;
import java.util.Vector;

import org.eclipse.jface.action.IContributionItem;
import org.eclipse.ui.actions.CompoundContributionItem;
import org.eclipse.ui.menus.CommandContributionItem;
import org.eclipse.ui.menus.CommandContributionItemParameter;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A contribution item, that displays a list of specs, recently loaded by the spec manager
 *
 * @author zambrovski
 */
public class SpecListContributionItem extends CompoundContributionItem
{
    /**
     * @see org.eclipse.ui.actions.CompoundContributionItem#getContributionItems()
     */
    protected IContributionItem[] getContributionItems()
    {

        Spec[] specs = Activator.getSpecManager().getRecentlyOpened();
        Vector specContributions = new Vector();

        for (int i = 0; i < specs.length; i++)
        {

            HashMap parameters = new HashMap();
            // fill the spec name for the handler
            parameters.put(OpenSpecHandler.PARAM_SPEC, specs[i].getName());

            // create the contribution item
            CommandContributionItemParameter param = new CommandContributionItemParameter(UIHelper.getActiveWindow(),
                    "toolbox.command.spec.open." + specs[i].getName(), OpenSpecHandler.COMMAND_ID, parameters, null, null, null,
                    specs[i].getName(), null, "Opens " + specs[i].getName(), CommandContributionItem.STYLE_PUSH, null,
                    true);
            
            // add contribution item to the list
            specContributions.add(new CommandContributionItem(param));

        }
        return (IContributionItem[]) specContributions.toArray(new IContributionItem[specContributions.size()]);
    }

}
