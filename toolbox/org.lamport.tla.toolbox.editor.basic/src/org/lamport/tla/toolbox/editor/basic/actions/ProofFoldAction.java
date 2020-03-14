package org.lamport.tla.toolbox.editor.basic.actions;

import java.util.ResourceBundle;

import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.custom.CaretEvent;
import org.eclipse.swt.custom.CaretListener;
import org.eclipse.ui.texteditor.ResourceAction;
import org.eclipse.ui.texteditor.TextEditorAction;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;

/**
 * Action for collapsing and expanding proofs in TLA modules.
 * 
 * @author Daniel Ricketts
 *
 */
public class ProofFoldAction extends TextEditorAction implements CaretListener, ISelectionChangedListener
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
    public ProofFoldAction(ResourceBundle bundle, String prefix, TLAEditor editor)
    {
        super(bundle, prefix, editor);
        editor.getViewer().getTextWidget().addCaretListener(this);
        editor.getSelectionProvider().addSelectionChangedListener(this);
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
        if (getTextEditor() instanceof TLAEditor)
        {
            TLAEditor editor = (TLAEditor) getTextEditor();
            if (editor.getProofStructureProvider() != null)
            {
                setEnabled(editor.getProofStructureProvider().canRunFoldOperation(getActionDefinitionId(),
                        (ITextSelection) editor.getSelectionProvider().getSelection()));
            }
        }
    }

    public void caretMoved(CaretEvent event)
    {
        update();
    }

    public void selectionChanged(SelectionChangedEvent event)
    {
        if (getTextEditor() instanceof TLAEditor)
        {
            TLAEditor editor = (TLAEditor) getTextEditor();
            if (editor.getProofStructureProvider() != null)
            {
                setEnabled(editor.getProofStructureProvider().canRunFoldOperation(getActionDefinitionId(),
                        (ITextSelection) event.getSelection()));
            }
        }
    }

}
