package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.VerifyKeyListener;
import org.eclipse.swt.events.FocusEvent;
import org.eclipse.swt.events.FocusListener;
import org.eclipse.swt.events.VerifyEvent;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;

/**
 * Performs a useless command to illustrate how to get keyboard input
 * and modify the contents of an editor.
 * 
 * @author Daniel Ricketts
 *
 */
public class ExampleEditCommandHandler extends AbstractHandler implements VerifyKeyListener, FocusListener
{

    private TLAEditor editor;

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        editor = EditorUtil.getTLAEditorWithFocus();
        if (editor != null)
        {
            install();
        }

        return null;
    }

    /**
     * Listens for the first key to be pressed. If it is a digit, it
     * finds the word currently containing the caret and repeats that word
     * the number of times equal to the digit pressed. If the key pressed
     * is not a digit, this does nothing to the document and
     * removes itself from subsequent key events.
     */
    public void verifyKey(VerifyEvent event)
    {
        try
        {
            // no other listeners should respond to this event
            event.doit = false;
            

            // the state mask indicates what modifier keys (such as CTRL) were being
            // pressed when the character was pressed
            if (event.stateMask == SWT.NONE && Character.isDigit(event.character))
            {
                // get the digit input
                int input = Character.getNumericValue(event.character);

                // get the text selection
                ISelection selection = editor.getSelectionProvider().getSelection();
                if (selection != null && selection instanceof ITextSelection)
                {
                    ITextSelection textSelection = (ITextSelection) selection;

                    IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());

                    // if one or more characters are selected, do nothing
                    if (textSelection.getLength() == 0 && document != null)
                    {

                        // retrieve the region describing the word containing
                        // the caret
                        IRegion region = DocumentHelper.getRegionExpandedBoth(document, textSelection.getOffset(),
                                DocumentHelper.getDefaultWordDetector());
                        try
                        {

                            // generate the insertion string
                            String insertionText = " " + document.get(region.getOffset(), region.getLength());
                            StringBuilder sb = new StringBuilder();
                            for (int i = 0; i < input; i++)
                            {
                                sb.append(insertionText);
                            }
                            document.replace(region.getOffset() + region.getLength(), 0, sb.toString());
                        } catch (BadLocationException e)
                        {
                            // TODO Auto-generated catch block
                            e.printStackTrace();
                        }
                    }
                }
            }
        } finally
        {

            uninstall();
        }
    }

    /**
     * This should never be called. The handler
     * should only be listening if there already is focus
     * and should be removed as a listener when focus
     * is lost.
     */
    public void focusGained(FocusEvent e)
    {
        // TODO Auto-generated method stub

    }

    /**
     * Uninstalls the handler.
     */
    public void focusLost(FocusEvent e)
    {
        uninstall();
    }

    /**
     * Should be called when the handler starts listening
     * for key strokes.
     * 
     * Adds this as a key stroke listener, adds to focus listeners
     * of the underlying text widget of the editor, and sets the
     * status line.
     * 
     * This is added as a focus listener so that it can uninstall()
     * itself if focus is lost.
     */
    private void install()
    {
        editor.getViewer().prependVerifyKeyListener(this);
        editor.getViewer().getTextWidget().addFocusListener(this);
        editor.setStatusMessage("Example command.");
    }

    /**
     * Should be called when the handler is done listening for
     * key strokes.
     * 
     * Removes itself as a key stroke listener, a focus listener, and sets
     * the status line to the empty string.
     */
    private void uninstall()
    {
        // do not listen to any other key strokes
        editor.getViewer().removeVerifyKeyListener(this);

        editor.getViewer().getTextWidget().removeFocusListener(this);

        editor.setStatusMessage("");
    }

}
