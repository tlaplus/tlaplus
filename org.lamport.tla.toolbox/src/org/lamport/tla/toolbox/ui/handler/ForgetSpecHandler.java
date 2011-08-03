package org.lamport.tla.toolbox.ui.handler;

import java.util.HashMap;
import java.util.Iterator;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchPage;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.ui.navigator.ToolboxExplorer;
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Forget specification.
 * 
 * This class is a clone of the DeleteSpecHandler method, except that the
 * ToolboxJob calls Activator.getSpecManager().removeSpec with the different
 * third argument that causes the .toolbox directory not to be deleted.
 * Strings were also appropriately changed.  I was unable to figure out how
 * to use a single handler for both the Forget and the Delete commands.
 *
 * 
 * @author Leslie Lamport
 * @version $Id$
 */
public class ForgetSpecHandler extends AbstractHandler implements IHandler
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
            ISelection selection = activePage.getSelection(ToolboxExplorer.VIEW_ID);
            if (selection != null && selection instanceof IStructuredSelection
                    && !((IStructuredSelection) selection).isEmpty())
            {
                
                Iterator<Spec> selectionIterator = ((IStructuredSelection) selection).iterator();
                while (selectionIterator.hasNext()) 
                {
                    final Spec spec = selectionIterator.next();
                    boolean answer = MessageDialog.openQuestion(UIHelper.getShellProvider().getShell(), "Forget specification?",
                            "Do you really want to remove specification " + spec.getName() + " from the Toolbox's list of specs?");
                    if (answer)
                    {
                    	// close the spec handler (in the ui thread)
                    	final WorkspaceSpecManager specManager = Activator.getSpecManager();
                        if (specManager.isSpecLoaded(spec)) {
                            UIHelper.runCommand(CloseSpecHandler.COMMAND_ID, new HashMap<String, String>());
                        }
                    	
    					// use confirmed rename -> rename
    					final Job j = new ToolboxJob("Deleting spec...") {
    						protected IStatus run(final IProgressMonitor monitor) {
    							Activator.getSpecManager().removeSpec(spec, monitor, true);
    							return Status.OK_STATUS;
    						}
    					};
    					j.schedule();
                    }
                }
            }
        }

        
        return null;
    }

    
}
