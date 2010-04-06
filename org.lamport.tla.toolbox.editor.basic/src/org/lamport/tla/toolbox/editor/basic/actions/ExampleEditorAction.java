package org.lamport.tla.toolbox.editor.basic.actions;

import java.util.ResourceBundle;

import org.eclipse.jface.action.IStatusLineManager;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.VerifyKeyListener;
import org.eclipse.swt.events.VerifyEvent;
import org.eclipse.ui.texteditor.TextEditorAction;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;

public class ExampleEditorAction extends TextEditorAction implements VerifyKeyListener
{

    private IStatusLineManager statusLine;

    public ExampleEditorAction(ResourceBundle bundle, String prefix, TLAEditor editor, IStatusLineManager statusLine)
    {
        super(bundle, prefix, editor);
        this.statusLine = statusLine;
    }

    /**
     * Installs this as a verify key listener on the editor's text viewer.
     */
    public void run()
    {
        ((TLAEditor) getTextEditor()).getViewer().prependVerifyKeyListener(this);
        statusLine.setMessage("Example Command");
    }

    /**
     * Listens for the first key to be pressed. If it is a digit, it
     * finds the word currently containing the caret and repeats that word
     * the number of times equal to the digit pressed.
     */
    public void verifyKey(VerifyEvent event)
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
            ISelection selection = getTextEditor().getSelectionProvider().getSelection();
            if (selection != null && selection instanceof ITextSelection)
            {
                ITextSelection textSelection = (ITextSelection) selection;

                IDocument document = getTextEditor().getDocumentProvider()
                        .getDocument(getTextEditor().getEditorInput());

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

        // do not listen to any other key strokes
        ((TLAEditor) getTextEditor()).getViewer().removeVerifyKeyListener(this);

        statusLine.setMessage("");
    }
}
