package org.lamport.tla.toolbox.editor.basic.actions;

import java.util.ResourceBundle;

import org.eclipse.ui.texteditor.ITextEditor;
import org.eclipse.ui.texteditor.ResourceAction;
import org.eclipse.ui.texteditor.TextEditorAction;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;

/**
 * Action for collapsing and expanding proofs in TLA modules.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProofFoldAction extends TextEditorAction
{

    /**
     * Creates and initializes the action for the given text editor. The action
     * configures its visual representation from the given resource bundle.
     *
     * @param bundle the resource bundle
     * @param prefix a prefix to be prepended to the various resource keys
     *   (described in <code>ResourceAction</code> constructor), or
     *   <code>null</code> if none
     * @param editor the text editor
     * @see ResourceAction#ResourceAction(ResourceBundle, String, int)
     */
    public ProofFoldAction(ResourceBundle bundle, String prefix, ITextEditor editor)
    {
        super(bundle, prefix, editor);
    }

    /**
     * If the caret is located within a proof, collapses and
     * expands the appropriate proofs.
     */
    public void run()
    {
        if (getTextEditor() instanceof TLAEditor)
        {
            TLAEditor editor = (TLAEditor) getTextEditor();
            editor.runFoldOperation(getActionDefinitionId());
        }
    }
    
    public void update()
    {
        super.update();
        
    }
    
    public boolean isEnabled()
    {
        return true;
    }

}
