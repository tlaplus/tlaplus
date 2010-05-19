/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.TheoremNode;
import tla2sany.st.Location;

/**
 * @author lamport
 *
 */
public class RenumberProofHandler extends AbstractHandler implements IHandler
{
    private IDocument doc; // The document in the editor.
    private String text; // The document as a string.
    private ISelectionProvider selectionProvider; // 
    private TextSelection selection; // The current selection.
    private TheoremNode node; // The selected node

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // Set the fields and return if we didn't get
        // a TheoremNode.
        if (!setFields())
        {
            return null;
        }

        try
        {
            IRegion iregion = AdapterFactory.locationToRegion(doc, node.getLocation()); 
            selectionProvider.setSelection(new TextSelection(iregion.getOffset(), iregion.getLength()));
        } catch (BadLocationException e)
        {

        }
        resetFields();
        return null;
    }

    /* Reprogram to disable or enable the command depending on whether the 
     * cursor is in a step that has a non-leaf proof.
     * (non-Javadoc)
     * @see org.eclipse.core.commands.AbstractHandler#setEnabled(java.lang.Object)
     */
    public void setEnabled(Object context)
    {
        setBaseEnabled(true);
    }

    /*
     * Sets the fields used by execute and setEnabled methods.  Returns false
     * iff it failed to set some field to a useful value;
     */
    private boolean setFields()
    {
        // The following code copied with minor modifications from BoxedCommentHandler
        TLAEditor editor;
        editor = EditorUtil.getTLAEditorWithFocus();
        // gets the editor to which command applies
        if (editor == null)
        {
            return false;
        }
        doc = editor.getDocumentProvider().getDocument(editor.getEditorInput());
        text = doc.get();
        selectionProvider = editor.getSelectionProvider();
        selection = (TextSelection) selectionProvider.getSelection();
        node = EditorUtil.getCurrentTheoremNode();
        if (node == null)
        {
            return false;
        }
        return true;
    }

    /*
     * Unsets the fields to save space.
     */
    private void resetFields()
    {
        doc = null;
        text = null;
        selectionProvider = null;
        selection = null;
        node = null;

    }
}
