package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.action.IAction;
import org.eclipse.ui.dialogs.PropertyDialogAction;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * @author Simon Zambrovski
 * @version $Id$
 * @deprecated is not used for two reasons: because there
 *             are no module properties, and it doesn't
 *             need to be used if we add some because we're
 *             using the default handler.
 */
public class ModulePropertiesHandler extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {

        IAction action = new PropertyDialogAction(UIHelper.getShellProvider(), UIHelper
                .getActiveEditorFileSelectionProvider());
        action.run();

        return null;
    }
}
