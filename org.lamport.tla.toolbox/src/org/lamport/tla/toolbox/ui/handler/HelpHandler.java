package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.swt.custom.BusyIndicator;
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
        // This may take a while, so use the busy indicator
        BusyIndicator.showWhile(null, new Runnable() {
            public void run() {
                UIHelper.getActiveWindow().getWorkbench().getHelpSystem().displayDynamicHelp();
            }
        });
        return null;
    }

}
