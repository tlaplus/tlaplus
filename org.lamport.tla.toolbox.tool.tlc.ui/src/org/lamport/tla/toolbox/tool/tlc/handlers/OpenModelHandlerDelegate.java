package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

public class OpenModelHandlerDelegate extends AbstractHandler implements IHandler
{
    public final static String COMMAND_ID = "toolbox.command.cnf.open.delegate";

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
            if (selected instanceof ILaunchConfiguration)
            {
                Map<String, String> parameters = new HashMap<String, String>();

                String modelNameUser = ModelHelper.getModelName(((ILaunchConfiguration) selected).getFile());

                // fill the model name for the handler
                parameters.put(OpenModelHandler.PARAM_MODEL_NAME, modelNameUser);
                // delegate the call to the open model handler
                UIHelper.runCommand(OpenModelHandler.COMMAND_ID, parameters);
            }
        }
        return null;
    }

}
