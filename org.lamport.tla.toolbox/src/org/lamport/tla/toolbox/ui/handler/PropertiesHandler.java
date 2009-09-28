package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.action.IAction;
import org.eclipse.ui.dialogs.PropertyDialogAction;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Opens the properties dialog, the underlying object is fetched by the passed ISelectionProvider
 * Currently it only returns selected Specs
 *  
 *  
 * @author Simon Zambrovski
 * @version $Id$
 * @deprecated  is not used any more; we're using the default handler.
 */
public class PropertiesHandler extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {

        
        // FIXME Fix the selection of specs only
        IAction action = new PropertyDialogAction(UIHelper.getShellProvider(), Activator.getSpecManager());
        // IAction action = new PropertyDialogAction(UIHelper.getShellProvider(), HandlerUtil.getActivePart(event));
        action.run();
        
        return null;
    }

}
