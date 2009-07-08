package org.lamport.tla.toolbox.tool.tlc.ui.contribution;

import org.eclipse.jface.action.ActionContributionItem;
import org.eclipse.jface.action.IAction;

/**
 * An action contribution item that is dynamic (can react on internal state changes)
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DynamicContributionItem extends ActionContributionItem
{
    public DynamicContributionItem(IAction action)
    {
        super(action);
    }
    public boolean isDynamic()
    {
        return true;
    }
}
