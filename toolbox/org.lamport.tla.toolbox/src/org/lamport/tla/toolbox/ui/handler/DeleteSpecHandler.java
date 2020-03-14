package org.lamport.tla.toolbox.ui.handler;

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
 * Delete specifications.
 * 
 * This command removes the spec from the Toolbox's list of specs and
 * deletes the .toolbox directory.  Class modified slightly by LL
 * on 3 August 2011 because of the addition of the Forget command.
 * 
 * @author Simon Zambrovski
 */
public class DeleteSpecHandler extends AbstractHandler implements IHandler {
    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
	public Object execute(ExecutionEvent event) throws ExecutionException {
         /*
         * No parameter try to get it from active navigator if any
         */
		final IWorkbenchPage activePage = UIHelper.getActivePage();
		if (activePage != null) {
            final ISelection selection = activePage.getSelection(ToolboxExplorer.VIEW_ID);
			if ((selection != null) && (selection instanceof IStructuredSelection)
					&& !((IStructuredSelection) selection).isEmpty()) {
                final Iterator<?> selectionIterator = ((IStructuredSelection) selection).iterator();
				while (selectionIterator.hasNext()) {
                	final Object next = selectionIterator.next();
                	if (!(next instanceof Spec)) {
                		// The selection can contain models and groups too.
                		continue;
                	}
                	
                    final Spec spec = (Spec) next;
                    // 3 Aug 2011: LL changed the dialog's message to make it clearer what the Delete command does.
                    final boolean answer
                    	= MessageDialog.openQuestion(UIHelper.getShellProvider().getShell(),
                    								 "Delete specification?",
                    								 "Do you really want the Toolbox to forget the specification "
                    										 		+ spec.getName() + " and delete all its models?");
					if (answer) {
                    	// close the spec handler (in the ui thread)
                    	final WorkspaceSpecManager specManager = Activator.getSpecManager();
                        if (specManager.isSpecLoaded(spec)) {
                        	final CloseSpecHandler handler = new CloseSpecHandler();
                        	final Boolean result = (Boolean)handler.execute(event);
                        	
                        	if ((result != null) && !result.booleanValue()) {
                        		// there was a dirty editor and the user cancelled out of the closing
                        		return null;
                        	}
                        }
                    	
    					final Job j = new ToolboxJob("Deleting spec...") {
    						protected IStatus run(final IProgressMonitor monitor) {
    							Activator.getSpecManager().removeSpec(spec, monitor, false);
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

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		if (UIHelper.getActivePage() == null) {
			return false;
		}
		return super.isEnabled();
	}
}
