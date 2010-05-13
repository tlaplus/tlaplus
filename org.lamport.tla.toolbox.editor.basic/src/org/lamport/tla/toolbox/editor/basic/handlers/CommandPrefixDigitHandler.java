/**
 * Certain commands take a numeric prefix argument.  This argument
 * generally specifies the number of times the command should be repeated.
 * For example, giving a prefix argument of 42 to a command to move down a line
 * should move down 42 lines.  This prefix argument is entered by typing
 * Alt+4 followed by Alt+2 before typing the command.  
 * 
 * A prefix argument that is not immediately followed by a command should
 * be cleared if followed by some command that does not use the prefix
 * argument.  This is approximated by clearing any prefix typed so far
 * if the current selection has changed has changed since the prefix was
 * typed.  Thus if you type Alt+4, click somewhere else in the editor, then
 * type Alt+2, then the current prefix becomes 2 rather than 42.  
 * 
 * The absence of a prefix command is generally equivalent to a prefix of 1.
 * 
 * A command that uses the prefix for the number of times it should be repeated
 * calls the getAndResetRepeatValue method.
 * 
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;

/**
 * @author lamport
 *
 */
public class CommandPrefixDigitHandler extends AbstractHandler implements IHandler
{  
//    public static String alt1Id = "org.lamport.tla.toolbox.editor.basic.alt1" ;
//    public static String alt2Id = "org.lamport.tla.toolbox.editor.basic.alt2" ;
//    public static String alt3Id = "org.lamport.tla.toolbox.editor.basic.alt3" ;
//    public static String alt4Id = "org.lamport.tla.toolbox.editor.basic.alt4" ;
//    public static String alt5Id = "org.lamport.tla.toolbox.editor.basic.alt5" ;
//    public static String alt6Id = "org.lamport.tla.toolbox.editor.basic.alt6" ;
//    public static String alt7Id = "org.lamport.tla.toolbox.editor.basic.alt7" ;
//    public static String alt8Id = "org.lamport.tla.toolbox.editor.basic.alt8" ;
//    public static String alt9Id = "org.lamport.tla.toolbox.editor.basic.alt9" ;
//    public static String alt0Id = "org.lamport.tla.toolbox.editor.basic.alt0" ;

//    private TLAEditor editor;
//      private IDocument doc ;                          // The document being edited.
//    private ISelectionProvider selectionProvider ;   //
    private  static boolean existsPrefix = false ; //
       // True iff a prefix value has been or is being typed.
    private  static int prefixValue = 0 ; // The current prefix value 
//    private TextSelection selection ;                // The current selection.
    private static TextSelection lastSelection = new TextSelection(-1, -1);            
      // The selection when handler last called.

    // private int offset ;                           // The current offset.
   // private IRegion lineInfo ;                     // The lineInfo for the current offset.

    /* (non-Javadoc)
     * The execute method is called when Alt plus a digit is typed.
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        TLAEditor editor = EditorUtil.getTLAEditorWithFocus() ;  // gets the editor to which command applies
        if (editor == null) {
            return null;
        }
        
   //     doc = editor.getDocumentProvider().getDocument(editor.getEditorInput());  // gets document being edited.
        ISelectionProvider selectionProvider = editor.getSelectionProvider() ;
        TextSelection selection = (TextSelection) selectionProvider.getSelection();
        
        // reset the prefix if the selection has changed
        if (existsPrefix && !selection.equals(lastSelection)) {
            existsPrefix = false;
            
            prefixValue = 0;
        }
        lastSelection = selection;
        String cmdId = event.getCommand().getId();
        int digit = Integer.parseInt(cmdId.substring(cmdId.length()-1));
        prefixValue = 10*prefixValue + digit;
        existsPrefix = true;
   //     offset = selection.getOffset();
        // TODO Auto-generated method stub
        return null;
    }
    
    /*
     * Returns the number of repetitions specified by the 
     * current prefix, which is 1 if there is no current prefix,
     * and it resets the current prefix.
     */
    
    public static int getAndResetRepeatValue(TLAEditor ed) {
        int returnVal = prefixValue;
        if (    (!existsPrefix)
             || (!lastSelection.equals((TextSelection) 
                     ed.getSelectionProvider().getSelection()) )  ) {
            returnVal = 1;
        }
        existsPrefix = false;
        prefixValue = 0;
        return returnVal;
    }
 

}
