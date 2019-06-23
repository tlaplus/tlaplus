package org.lamport.tla.toolbox.tool.prover.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;

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

    /**
     * This handler is enabled if there is a TLA editor with focus and a TLAPM executable exists.
     */
    public void setEnabled(Object context)
    {
        final ResourceHelper.TLAPMExecutablePaths ep = ResourceHelper.getExecutablePaths();

        setBaseEnabled((EditorUtil.getTLAEditorWithFocus() != null) && ep.tlapmDoesExist());
    }
}
