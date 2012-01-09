package org.lamport.tla.toolbox.editor.basic.handlers;
import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.viewers.IColorDecorator;
import org.eclipse.swt.custom.CaretEvent;
import org.eclipse.swt.custom.CaretListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;

/**
 * 
 */

/**
 * This is a not-yet written handler for the Goto Matching Paren command, which is similar
 * to the Eclipse Ctl+Shift+P command, except that it reports mismatched parentheses as an
 * error.  The user puts the cursor to the right of the paren and the command moves to the 
 * right of the matching paren.  It handles the following matching paren pairs:
 * 
 *   ( )   [ ]   { }   << >>   (* *)
 * 
 * @author lamport
 *
 */
public class GotoMatchingParenHandler extends AbstractHandler implements
        IHandler {
    
    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException {
        TLAEditor tlaEditor = EditorUtil.getTLAEditorWithFocus();
        
        //Dummy code that just raises an error message.
        RGB rgb = new RGB(255,0,0);
        Color color = null; // new Color(null, rgb);
        ErrorMessageEraser listener = new ErrorMessageEraser(tlaEditor, color);
        tlaEditor.getViewer().getTextWidget().addCaretListener(listener);
        tlaEditor.getEditorSite().getActionBars().getStatusLineManager().setErrorMessage("Error message");
        
        tlaEditor.getViewer().setTextColor(color, 0, 10, true);
        ISourceViewer internalSourceViewer = tlaEditor.publicGetSourceViewer();
        IDocument document = internalSourceViewer.getDocument();
        internalSourceViewer.setRangeIndication(0, 10, false);
       
        return null;
    }

    private static class ErrorMessageEraser implements CaretListener{
        TLAEditor editor;
        Color color;
        
       private ErrorMessageEraser(TLAEditor e, Color col) {
            editor = e;
            color = col;
        }

       public void caretMoved(CaretEvent event) {
           // TODO Auto-generated method stub
           editor.getEditorSite().getActionBars().getStatusLineManager().setErrorMessage(
                   null);
           editor.getViewer().getTextWidget().removeCaretListener(this);
             editor.publicGetSourceViewer().removeRangeIndication();
//           editor.resetHighlightRange();
//           editor.showHighlightRangeOnly(false);
//           editor.getViewer().setTextColor(new Color(null, 0,0,0), 0, 10, true);
//           color.dispose();

       } 
    }
    
}
