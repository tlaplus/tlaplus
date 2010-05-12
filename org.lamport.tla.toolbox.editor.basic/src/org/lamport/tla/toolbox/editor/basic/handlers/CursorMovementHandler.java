/**
 *  This method is the handler for the following commands:
 *    Move Right One Character 
 *    Move Left One Character
 *  These commands take prefix arguments as described in the
 *  CommandPrefixDigitHandler class.
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import javax.swing.text.BadLocationException;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;

/**
 * @author lamport
 *
 */
public class CursorMovementHandler extends AbstractHandler implements IHandler
{
    /*
     * The following fields are used by the various methods for handling the commands
     * and are set when  the command is executed (by calling the handler's execute
     * method.
     */
    private IDocument doc ;                          // The document being edited.
    private ISelectionProvider selectionProvider ;   // 
    private TextSelection selection ;                // The current selection.
    private int offset ;                             // The current offset.
    private IRegion lineInfo ;                       // The lineInfo for the current offset.

    /*
     * The following are the command ids.
     */
    public final String charRightId = "org.lamport.tla.toolbox.editor.basic.charRight" ;
    public final String charLeftId = "org.lamport.tla.toolbox.editor.basic.charLeft";
    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    { TLAEditor editor ;
      editor = EditorUtil.getTLAEditorWithFocus() ;  // gets the editor to which command applies
      if (editor == null) {
          return null;
      }
      
      doc = editor.getDocumentProvider().getDocument(editor.getEditorInput());  // gets document being edited.
      selectionProvider = editor.getSelectionProvider() ;
      selection = (TextSelection) selectionProvider.getSelection();
      offset = selection.getOffset();
      if (offset < 0){
          return null;
      }
      try {
//          char nextChar = doc.getChar(offset);
//          System.out.println("-" + nextChar + "-");
//          if (nextChar == '\n') {
//              return null;
//          }
          lineInfo = doc.getLineInformationOfOffset(offset);

          String cmd = event.getCommand().getId(); 
          int repeatVal = 
                CommandPrefixDigitHandler.getAndResetRepeatValue(editor);
            while (repeatVal > 0)
            {
                repeatVal-- ;
                if (cmd.equals(charRightId))
                {
                    charRight();
                } else if (cmd.equals(charLeftId))
                {
                    charLeft();
                } else
                {
                    System.out.println("Unrecognized command.");
                    System.out.println(cmd);
                }
                System.out.println("Called with repeatVal = " + repeatVal);
            }
                      
      
          
      } catch (org.eclipse.jface.text.BadLocationException e) {
        return null;
      } 
     return null;
    }
    
    private void charRight() {
        if (offset < lineInfo.getOffset()+lineInfo.getLength()) {
            selectionProvider.setSelection(new TextSelection(offset+1,0));
            offset++;
        }
    }
    
    private void charLeft() {
        if (offset > lineInfo.getOffset()) {
            selectionProvider.setSelection(new TextSelection(offset-1,0));
            offset--;
        }
    }
}
