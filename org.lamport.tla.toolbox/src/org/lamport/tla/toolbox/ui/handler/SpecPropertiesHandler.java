package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.viewers.ISelection;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SpecPropertiesHandler extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
     
        System.out.println("Spec Props");
        
        ISelection selection = UIHelper.getActivePage().getSelection();
        
        return null;
    }

}
