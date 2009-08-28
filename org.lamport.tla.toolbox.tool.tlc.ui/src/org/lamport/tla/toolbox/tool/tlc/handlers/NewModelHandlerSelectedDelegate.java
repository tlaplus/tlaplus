package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Delegates the model creation for the spec selected from the toolbox explorer
 * @author Simon Zambrovski
 * @version $Id$
 */
public class NewModelHandlerSelectedDelegate extends AbstractHandler implements IHandler
{
    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        /*
         * Try to get the spec from active navigator if any
         */
        ISelection selection = HandlerUtil.getCurrentSelectionChecked(event);
        if (selection != null && selection instanceof IStructuredSelection
                && ((IStructuredSelection) selection).size() == 1)
        {
            Object selected = ((IStructuredSelection) selection).getFirstElement();
            if (selected instanceof Spec)
            {
                HashMap parameters = new HashMap();
                // fill the spec name for the handler
                parameters.put(NewModelHandler.PARAM_SPEC_NAME, ((Spec) selected).getName());
                // delegate the call to the new model handler
                UIHelper.runCommand(NewModelHandler.COMMAND_ID, parameters);
            }
        }
        return null;
    }

}
