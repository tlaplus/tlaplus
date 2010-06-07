package org.lamport.tla.toolbox.tool.prover.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

/**
 * Checks the proof step currently containing the caret. Does
 * not launch the prover if the caret is not at a step. Instead,
 * it shows a message to the user explaining this. See the comments
 * in the execute method for how it works.
 * 
 * Does nothing if the module has parse errors.
 * 
 * @author Daniel Ricketts
 *
 */
public class CheckProofHandler extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        /*
         * See the comments for the following method for its
         * effect and implementation.
         */
        ProverHelper.runProverForActiveSelection(false);

        return null;
    }
}
