package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.ui.IWorkbenchPage;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.provider.ToolboxExplorer;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Handler for renaming the specifications
 * @author Simon Zambrovski
 * @version $Id$
 */
public class RenameSpecHandler extends AbstractHandler implements IHandler
{
    private String specName;

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
            ISelection selection = activePage.getSelection(ToolboxExplorer.VIEW_ID);
            if (selection != null && selection instanceof IStructuredSelection)
            {
                Spec spec = (Spec) ((IStructuredSelection) selection).getFirstElement();
                
                specName = spec.getName() + "_Copy";
                
                IInputValidator specNameInputValidator = new SpecNameValidator();
                final InputDialog dialog = new InputDialog(UIHelper.getShellProvider().getShell(), "New specification name",
                        "Please input the new name of the specification", specName, specNameInputValidator);
                dialog.setBlockOnOpen(true);
                UIHelper.runUISync(new Runnable() {

                    public void run()
                    {
                        int open = dialog.open();
                        switch (open) {
                        case Window.OK:
                            specName = dialog.getValue();
                            break;
                        case Window.CANCEL:
                            // cancel model creation
                            specName = null;
                        }
                    }
                });
                if (specName == null)
                {
                    // exit processing if no specName at place
                    return null;
                }
                System.out.println("Rename " + spec.getName() + " to " + specName);
                Activator.getSpecManager().renameSpec(spec, specName);
            } 
        }

        return null;
    }

    
    class SpecNameValidator implements IInputValidator
    {

        /* (non-Javadoc)
         * @see org.eclipse.jface.dialogs.IInputValidator#isValid(java.lang.String)
         */
        public String isValid(String name)
        {
            if (name == null || name.isEmpty())
            {
                return "The specification name must be not empty";
            }
            Spec spec = Activator.getSpecManager().getSpecByName(name);
            if (spec !=null) 
            {
                if (spec == Activator.getSpecManager().getSpecLoaded()) 
                {
                    return "The specification can not be renamed to its own name";
                } else 
                {
                    return "The specification with this name already exists";
                }
            }
            return null;
        }
        
    }
}
