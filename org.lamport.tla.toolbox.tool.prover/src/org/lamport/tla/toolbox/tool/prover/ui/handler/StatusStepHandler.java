package org.lamport.tla.toolbox.tool.prover.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;

/**
 * Runs the prover to simply get the status of the step containing
 * the current selection in the active TLA Editor.
 * 
 * See {@link ProverHelper#runProverForActiveSelection(boolean, boolean)}
 * for more information.
 * 
 * @author Daniel Ricketts
 *
 */
public class StatusStepHandler extends AbstractHandler implements IHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        ProverHelper.runProverForActiveSelection(true, false);

        return null;
    }

}
