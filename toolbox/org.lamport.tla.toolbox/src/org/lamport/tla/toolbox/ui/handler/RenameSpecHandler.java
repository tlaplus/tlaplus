package org.lamport.tla.toolbox.ui.handler;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.IInputValidator;
import org.eclipse.jface.dialogs.InputDialog;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.ui.IWorkbenchPage;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.ui.navigator.ToolboxExplorer;
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Handler for renaming the specifications
 */
public class RenameSpecHandler extends AbstractHandler implements IHandler {

	private boolean reopenEditorAfterRename;

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		/*
		 * No parameter try to get it from active navigator if any
		 */
		final IWorkbenchPage activePage = UIHelper.getActivePage();
		if (activePage != null) {
			final ISelection selection = activePage.getSelection(ToolboxExplorer.VIEW_ID);
			if (selection != null && selection instanceof IStructuredSelection) {
				// handler is set up to only allow single selection in
				// plugin.xml -> no need to handle multi selection
				final Spec spec = (Spec) ((IStructuredSelection) selection).getFirstElement();

				// name proposal
				String specName = spec.getName() + "_Copy";

				// dialog that prompts the user for the new spec name (no need
				// to join UI thread, this is the UI thread)
				final InputDialog dialog = new InputDialog(UIHelper.getShell(), "New specification name",
						"Please input the new name of the specification", specName, new SpecNameValidator());
				dialog.setBlockOnOpen(true);
				if (dialog.open() == Window.OK) {
					final WorkspaceSpecManager specManager = Activator.getSpecManager();
					
					// close open spec before it gets renamed
					reopenEditorAfterRename = false;
					if (specManager.isSpecLoaded(spec)) {
						UIHelper.runCommand(CloseSpecHandler.COMMAND_ID, new HashMap<String, String>());
						reopenEditorAfterRename = true;
					}
					
					// use confirmed rename -> rename
					final Job j = new ToolboxJob("Renaming spec...") {
						protected IStatus run(final IProgressMonitor monitor) {
							// do the actual rename
							specManager.renameSpec(spec, dialog.getValue(), monitor);
							
							// reopen editor again (has to happen in UI thread)
							UIHelper.runUIAsync(new Runnable() {
								/* (non-Javadoc)
								 * @see java.lang.Runnable#run()
								 */
								public void run() {
									if (reopenEditorAfterRename) {
										Map<String, String> parameters = new HashMap<String, String>();
										parameters.put(OpenSpecHandler.PARAM_SPEC, dialog.getValue());
										UIHelper.runCommand(OpenSpecHandler.COMMAND_ID, parameters);
									}
								}
							});
							return Status.OK_STATUS;
						}
					};
					j.schedule();
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

	class SpecNameValidator implements IInputValidator {

		/* (non-Javadoc)
		 * @see org.eclipse.jface.dialogs.IInputValidator#isValid(java.lang.String)
		 */
		public String isValid(String name) {
			// null, empty, just whitespaces
			if (name == null || name.length() == 0 || name.trim().length() == 0) {
				return "The specification name must not be empty";
			}
			final Spec[] specs = Activator.getSpecManager().getRecentlyOpened();
			for (int i = 0; i < specs.length; i++) {
				if (name.equals(specs[i].getName())) {
					return "The specification with this name already exists";
				}
				if (name.equalsIgnoreCase(specs[i].getName())) {
					return "A specification exists with the same name but a different case. This is not allowed.";
				}
			}
			return null;
		}

	}
}
