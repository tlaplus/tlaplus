package org.lamport.tla.toolbox.ui.handler;

import java.util.List;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.expressions.IEvaluationContext;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.util.ToolboxJob;

import util.TLAConstants;

/**
 * If a module is selected and it is not the main module of the specification, facilitate its deletion.
 */
public class DeleteModuleHandler extends AbstractHandler {
	private boolean m_enabled = false;
	
    /**
     * {@inheritDoc}
     */
	@Override
	public void setEnabled(final Object evaluationContext) {
		final Module m = getModuleFromContext((IEvaluationContext)evaluationContext);
		
		if (m != null) {
        	final WorkspaceSpecManager specManager = Activator.getSpecManager();
        	final Spec loadedSpec = specManager.getSpecLoaded();
        	final String specName = loadedSpec.getName();
        	final String moduleName = m.getModuleName();
        	
        	m_enabled = !specName.equals(moduleName);
        	
        	return;
		}
		
		m_enabled = false;
	}
	
    /**
     * {@inheritDoc}
     */
	@Override
	public boolean isEnabled() {
		return m_enabled;
	}
	
    /**
     * {@inheritDoc}
     */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		final Module m = getModuleFromContext((IEvaluationContext)event.getApplicationContext());
		final Job j = new ToolboxJob("Removing module...") {
			protected IStatus run(final IProgressMonitor monitor) {
				try {
					m.getResource().delete(IResource.NEVER_DELETE_PROJECT_CONTENT, monitor);
					return Status.OK_STATUS;
				} catch (Exception e) {
					return Status.CANCEL_STATUS;
				}
			}
		};
		final IWorkbenchWindow iww = PlatformUI.getWorkbench().getActiveWorkbenchWindow();
		final IWorkbenchPage page = iww.getActivePage();
		final IEditorReference[] refs = page.getEditorReferences();
		final String tabName = m.getModuleName() + TLAConstants.Files.TLA_EXTENSION;
		boolean removeModule = true;
		for (final IEditorReference ier : refs) {
			if (tabName.equals(ier.getName())) {
				final IEditorPart editor = ier.getEditor(false);
				
				if (editor != null) {
					// If dirty and they cancel the closing, this will return false
					removeModule = page.closeEditor(editor, true);
				}
			}
		}
		
		if (removeModule) {
			j.schedule();
		}
		
		return null;
	}
	
	private Module getModuleFromContext(final IEvaluationContext context) {
		final Object defaultVariable = context.getDefaultVariable();
		
		if (defaultVariable instanceof List) {
			final List<?> list = (List<?>)defaultVariable;
			
			if (list.size() == 1) {
				final Object o = list.get(0);
				
				if (o instanceof Module) {
					return (Module)o;
				}
			}
		}
		
		return null;
	}
}
