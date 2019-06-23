package org.lamport.tla.toolbox.tool.prover.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.tool.prover.ui.util.ProverHelper;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Launches TLAPM on the proof step currently containing the caret or on the
 * entire module if the caret is not at a proof step. See 
 * @link ProverHelper#runProverForActiveSelection(boolean, boolean)} to see how it works.
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
        ProverHelper.runProverForActiveSelection(false, true);

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
