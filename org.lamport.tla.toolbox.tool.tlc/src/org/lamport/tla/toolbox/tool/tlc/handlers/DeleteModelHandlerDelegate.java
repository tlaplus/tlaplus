package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchPage;
import org.lamport.tla.toolbox.tool.tlc.launch.ui.ModelExplorer;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

public class DeleteModelHandlerDelegate extends AbstractHandler implements IHandler
{

    /**
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
            ISelection selection = activePage.getSelection(ModelExplorer.VIEW_ID);
            if (selection != null && selection instanceof IStructuredSelection
                    && ((IStructuredSelection) selection).size() == 1)
            {
                Object selected = ((IStructuredSelection) selection).getFirstElement();
                String modelNameUser = ModelHelper.getModelName(((ILaunchConfiguration) selected).getFile());

                boolean answer = MessageDialog.openQuestion(UIHelper.getShellProvider().getShell(), "Delete model?",
                        "Do you really want to delete model " + modelNameUser + "?");
                if (answer)
                {
                    HashMap parameters = new HashMap();
                    
                    // fill the model name for the handler
                    parameters.put(DeleteModelHandler.PARAM_MODEL_NAME, modelNameUser);
                    
                    // delegate the call to the open model handler
                    UIHelper.runCommand(DeleteModelHandler.COMMAND_ID, parameters);
                }
            }
        }
        return null;
    }

}
