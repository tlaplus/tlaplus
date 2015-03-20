package org.lamport.tla.toolbox.ui.handler;

import java.util.HashMap;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.services.IEvaluationService;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;
import org.lamport.tla.toolbox.ui.expression.ParseErrorTester;
import org.lamport.tla.toolbox.ui.view.ProblemView;
import org.lamport.tla.toolbox.util.UIHelper;

public class OpenParseErrorViewHandler extends AbstractHandler implements IHandler {

	private final SpecLifecycleParticipant specLifecycleParticipant = new SpecLifecycleParticipant() {
		public boolean eventOccured(SpecEvent event) {
			if (event.getType() == SpecEvent.TYPE_PARSE) {
				final IEvaluationService evalService = (IEvaluationService) PlatformUI.getWorkbench().getService(
						IEvaluationService.class);
				evalService.requestEvaluation(ParseErrorTester.PROPERTY_ID);
			}
			return false;
		}
	};

	public OpenParseErrorViewHandler() {
		// Various (Eclipse foundation) UIs react to the parse status of the
		// currently active spec, but can't register as
		// SpecLifecycleParticipants (SLP is a Toolbox, not Eclipse foundation
		// concept). Thus, we have to let those UIs know about the status of a
		// spec.
		// It is created and registered here in the ToolboxExplorer because this
		// UI is always instantiated when the Toolbox starts.
		Activator.getSpecManager().addSpecLifecycleParticipant(specLifecycleParticipant);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.core.commands.AbstractHandler#dispose()
	 */
	public void dispose() {
		super.dispose();
		Activator.getSpecManager().removeSpecLifecycleParticipant(specLifecycleParticipant);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
	 */
	public Object execute(ExecutionEvent event) throws ExecutionException {
		HashMap<String, String> params = new HashMap<String, String>();
		params.put(OpenViewHandler.PARAM_VIEW_NAME, ProblemView.ID);
		UIHelper.runCommand(OpenViewHandler.COMMAND_ID, params);

		return null;
	}
}
