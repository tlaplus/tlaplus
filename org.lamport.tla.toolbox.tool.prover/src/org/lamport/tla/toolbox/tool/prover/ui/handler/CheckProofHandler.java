package org.lamport.tla.toolbox.tool.prover.ui.handler;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

/**
 * Launches TLAPM on the proof step currently containing the caret or on the
 * entire module if the caret is not at a proof step. See 
 * {@link ProverHelper#runProverForActiveSelection(boolean, boolean)} to see how it works.
 * 
 * @author Daniel Ricketts
 */
public class CheckProofHandler extends AbstractProverHandler implements IHandler {
	public Object execute(ExecutionEvent event) throws ExecutionException {
		/*
		 * See the comments for the following method for its effect and implementation.
		 */
		ProverHelper.runProverForActiveSelection(false, true);

		return null;
	}
}
