package org.lamport.tla.toolbox.ui.handler;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchPage;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Handler that opens the spec selected in the CNF and delegates to the open spec handler
 * @author Simon Zambrovski
 * @version $Id$
 */
public class OpenSpecHandlerDelegate extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {

        /*
         * Try to get the spec from active navigator if any
         */
        IWorkbenchPage activePage = UIHelper.getActivePage();
        if (activePage != null)
        {
            ISelection selection = activePage.getSelection("toolbox.view.SpecView");
            if (selection != null && selection instanceof IStructuredSelection
                    && ((IStructuredSelection) selection).size() == 1)
            {
                Object selected = ((IStructuredSelection) selection).getFirstElement();
                if (selected instanceof Spec)
                {
                    HashMap parameters = new HashMap();
                    // fill the spec name for the handler
                    parameters.put(OpenSpecHandler.PARAM_SPEC, ((Spec) selected).getName());

                    // delegate the call to the open spec handler
                    UIHelper.runCommand(OpenSpecHandler.COMMAND_ID, parameters);
                }
            }
        }

        return null;
    }

}
