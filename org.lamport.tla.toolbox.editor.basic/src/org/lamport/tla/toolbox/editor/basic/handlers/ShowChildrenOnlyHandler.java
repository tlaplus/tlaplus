package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.jface.text.ITextSelection;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.proof.IProofFoldCommandIds;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;

/**
 * Handler for command that shows all
 * children of the step currently containing the caret
 * and hides the proofs of those children.
 * 
 * @author Daniel Ricketts
 *
 */
public class ShowChildrenOnlyHandler extends ProofFoldCommandHandler
{

    /**
     * This method is used to update the enablement state. This has the
     * effect of graying out any menu items for the
     * command if the handler is disabled. Through experimentation, this method seems to be
     * called just before such menu items are rendered in the UI and
     * just before the handler is executed.
     */
    public void setEnabled(Object context)
    {
        TLAEditor editor = EditorUtil.getTLAEditorWithFocus();

        if (editor != null)
        {
            if (editor.getProofStructureProvider() != null)
            {
                setBaseEnabled(editor.getProofStructureProvider().canRunFoldOperation(
                        IProofFoldCommandIds.SHOW_IMMEDIATE,
                        (ITextSelection) editor.getSelectionProvider().getSelection()));
            }
        }
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
