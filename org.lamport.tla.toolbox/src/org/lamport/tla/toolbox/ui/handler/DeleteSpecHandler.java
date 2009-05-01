package org.lamport.tla.toolbox.ui.handler;

import java.util.Iterator;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchPage;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.UIHelper;

public class DeleteSpecHandler extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        
        
        /*
         * No parameter try to get it from active navigator if any
         */
        IWorkbenchPage activePage = UIHelper.getActivePage();
        if (activePage != null)
        {
            ISelection selection = activePage.getSelection("toolbox.view.SpecView");
            if (selection != null && selection instanceof IStructuredSelection
                    && !((IStructuredSelection) selection).isEmpty())
            {
                
                Iterator selectionIterator = ((IStructuredSelection) selection).iterator();
                while (selectionIterator.hasNext()) 
                {
                    Spec spec = (Spec) selectionIterator.next();
                    System.out.println("Delete " + spec.getName());   
                }
            }
        }

        
        return null;
    }

    
}
