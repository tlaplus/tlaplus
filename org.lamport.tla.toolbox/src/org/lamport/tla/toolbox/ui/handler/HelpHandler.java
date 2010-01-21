package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Handles the help 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class HelpHandler extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        UIHelper.showDynamicHelp();
        /*// This may take a while, so use the busy indicator
        BusyIndicator.showWhile(null, new Runnable() {
            public void run()
            {
                UIHelper.getActiveWindow().getWorkbench().getHelpSystem().displayDynamicHelp();
                // the following ensure that the help view receives focus
                // prior to adding this, it would not receive focus if
                // it was opened into a folder or was already
                // open in a folder in which another part had focus
                IViewPart helpView = UIHelper.findView("org.eclipse.help.ui.HelpView");
                if (helpView != null && UIHelper.getActiveWindow() != null
                        && UIHelper.getActiveWindow().getActivePage() != null)
                {
                    UIHelper.getActiveWindow().getActivePage().activate(helpView);
                }
            }
        });*/
        return null;
    }

}
