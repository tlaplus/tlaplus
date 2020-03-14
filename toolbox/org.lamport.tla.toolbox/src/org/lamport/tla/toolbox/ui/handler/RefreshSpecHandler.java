package org.lamport.tla.toolbox.ui.handler;

import java.util.Iterator;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IWorkbenchPage;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.navigator.ToolboxExplorer;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;

public class RefreshSpecHandler extends AbstractHandler {

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
	 */
	public Object execute(final ExecutionEvent event) throws ExecutionException {
		final IWorkbenchPage activePage = UIHelper.getActivePage();
		if (activePage != null) {
			final ISelection selection = activePage.getSelection(ToolboxExplorer.VIEW_ID);
			if (selection != null && selection instanceof IStructuredSelection
					&& !((IStructuredSelection) selection).isEmpty()) {

				final Job job = new ToolboxJob("Refreshing spec...") {
					/* (non-Javadoc)
					 * @see org.eclipse.core.runtime.jobs.Job#run(org.eclipse.core.runtime.IProgressMonitor)
					 */
					protected IStatus run(IProgressMonitor monitor) {
						final Iterator<Spec> selectionIterator = ((IStructuredSelection) selection).iterator();
						while (selectionIterator.hasNext()) {
							ResourceHelper.refreshSpec(selectionIterator.next(), monitor);
						}
						return Status.OK_STATUS;
					}
				};
				job.schedule();
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
