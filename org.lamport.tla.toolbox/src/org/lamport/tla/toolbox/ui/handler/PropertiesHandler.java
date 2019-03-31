package org.lamport.tla.toolbox.ui.handler;

import java.util.List;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.expressions.IEvaluationContext;
import org.eclipse.jface.action.IAction;
import org.eclipse.ui.dialogs.PropertyDialogAction;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Opens the properties dialog; the underlying object is fetched by the passed
 * ISelectionProvider. It only returns selected Specs.
 * 
 * @author Simon Zambrovski
 */
public class PropertiesHandler extends AbstractHandler {
	private boolean m_enabled = false;
	
    /**
     * {@inheritDoc}
     */
	@Override
	public void setEnabled(final Object evaluationContext) {
		final IEvaluationContext context = (IEvaluationContext)evaluationContext;
		final Object defaultVariable = context.getDefaultVariable();
		Spec spec = null;
		
		if (defaultVariable instanceof List) {
			final List<?> list = (List<?>)defaultVariable;
			
			if (list.size() == 1) {
				final Object o = list.get(0);
				
				if (o instanceof Spec) {
					spec = (Spec)o;
				}
			}
		}
		
		m_enabled = (spec != null);
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
		final IAction action = new PropertyDialogAction(UIHelper.getShellProvider(), Activator.getSpecManager());

		action.run();

		return null;
	}
}
