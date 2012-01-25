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
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchPage;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.ui.navigator.ToolboxExplorer;
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * Forget specification.
 * 
 * This class is a clone of the DeleteSpecHandler method, except that the
 * ToolboxJob calls Activator.getSpecManager().removeSpec with the different
 * third argument that causes the .toolbox directory not to be deleted.
 * Strings were also appropriately changed.  I was unable to figure out how
 * to use a single handler for both the Forget and the Delete commands.
 *
 * It would be nice if the confirmation dialog that the command popped up
 * contained a checkbox that allows the user to suppress the confirmation
 * dialog on future executions.  To allow the user to change his mind
 * and require confirmation, this requires that whether or not a confirmation
 * is raised be a user-settable preference.  (The main TLA+ preference pages is
 * currently the only preference page where it makes sense to put this preference.)
 * This can all be implemented as follows:
 * 
 *   - Add to the IPreferenceConstants class a definition like
 *   
 *        public static final String NO_CONFIRM_ON_FORGET = "doNotConfirmOnForget";
 *   
 *   - Add the appropriate command to set the preference's default value
 *     in the initializeDefaultPreferences method of the PreferenceInitializer
 *     class.
 * 
 *   - Add the preference selector to the TLA+ Preferences page by adding the 
 *     appropriate checkbox with the createFieldEditors method of the 
 *     GeneralPreferencePage class.  (Use the "Continue Previous Session on Restart"
 *     checkbox as a model.)
 *     
 *   - Create a ConfirmForgetDialog class that creates the dialog.  That class's
 *     okPressed method should set the preference if necessary.  See
 *     LaunchProverDialog for a model.
 *     
 *   - Modify the ForgetSpecHandler class's execution method so it first tests the 
 *     preference to see if it should launch the dialog.  I believe it does this with
 *     
 *         IPreferenceStore store = PreferenceStoreHelper.getInstancePreferenceStore();
 *         boolean shouldIgnore = store.getBoolean(IPreferenceConstants.NO_CONFIRM_ON_FORGET)
 *     
 *     If it should, the execution method then launches the dialog  and waits until the 
 *     user closes it.  See GeneralLaunchProverHandler class's execute method to see how 
 *     that's done.
 *     
 * I didn't add this feature because the TLA+ Preference page has so little on it
 * that it seems a shame to complicate it for such a trivial feature.  This decision
 * should be re-examined if additional features are added to that page.
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
