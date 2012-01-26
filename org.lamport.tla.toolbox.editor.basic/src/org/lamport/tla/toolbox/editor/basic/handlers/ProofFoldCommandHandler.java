package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;

/**
 * Abstract base handler for fold command handling.
 * 
 * Subclasses can extend by implementing the {@link ProofFoldCommandHandler#setEnabled(Object)} method
 * to enable and disable the handler. This has the effect of graying out any menu items for the
 * command if the handler is disabled. The {@link ProofFoldCommandHandler#setEnabled(Object)}
 * method seems to be called just before such menu items are rendered in the UI and
 * just before the handler is executed.
 * 
 * @author Daniel Ricketts
 *
 */
public abstract class ProofFoldCommandHandler extends AbstractHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        TLAEditor editor = EditorUtil.getTLAEditorWithFocus();

        if (editor != null)
        {
            editor.runFoldOperation(event.getCommand().getId());
        }

        return null;
    }
	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		if (EditorUtil.getTLAEditorWithFocus() == null) {
			return false;
		}
		return super.isEnabled();
	}

}
