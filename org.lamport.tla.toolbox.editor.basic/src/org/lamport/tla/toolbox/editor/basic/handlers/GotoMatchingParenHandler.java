package org.lamport.tla.toolbox.editor.basic.handlers;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.viewers.IColorDecorator;
import org.eclipse.swt.custom.CaretEvent;
import org.eclipse.swt.custom.CaretListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * 
 */

/**
 * This is the handler for the Goto Matching Paren command, which by default is bound
 * to Ctl+Shift+P.   THe command considers the following to be matching parens:
 * 
 *    ( )   [ ]   { }   << >>   (* *)  
 * 
 * If the cursor is immediately to the right of a paren, then it moves the cursor to the
 * right of the matching paren, except in case of error.  If there is an error, then the
 * cursor is not moved, an error message is put in the Toolbox's status bar (at the bottom
 * of the window), and if the error is an unmatched paren, the paren is highlighted with
 * an Annotation marker.  The error message and highlighting disappear when the cursor
 * is moved (or more precisely, when a CaretListener is called).
 * 
 * The text is divided into three regions:
 * 
 *  - Line comments (which follow a "\*" on a line)
 *  
 *  - Strings (outside line comments), which are delimited by " " .  A beginning quote
 *    with no matching end quote is considered to be a string that extends to the end
 *    of the line.  
 *  
 *  - The rest of the text.
 *  
 *  Matching considers only parens that appear in the same region as the selected paren.
 *  
 *  There is one problematic case: when the cursor is between the '(' and the '*' in
 *  "(*".  In that case, the cursor is considered not to be at a paren.
 * 
 * @author lamport
 *
 */
public class GotoMatchingParenHandler extends AbstractHandler implements
        IHandler {
    
    //
    public static String PAREN_ERROR_MARKER_TYPE = "org.lamport.tla.toolbox.editor.basic.showParenError";
    
    /**
     * This field holds the document of the module in which the action is
     * taking place.
     */
    private IDocument document;
    
    private int currLoc;
      // the current location of the parenthesis matching algorithm.
    private int regionType;
    // the type of the region being searched.
  
    // The following fields contain information about the regions of the
    // current line.
    private int currLineNum ;  // We may want to eliminate this and 
                               // pass the current location as an argument and result.
      // the number of the line (Java numbering)
    private int beginLineLoc ;
      // the offset of the beginning of the current line
    private int endLineLoc ;
      // the offset of the end of the current line, which
      // is the same as that of the beginning of the next
      // line except at the end of the document.
    private int lineCommentLoc;
      // if there is an end-of-line comment, this is
      // the offset of the beginning of the "\*";
      // otherwise, it equals endLineLoc
    private int[] leftQuoteLocs = new int[1000];
      // An array whose i-th element is the location of
      // (the left-side of) the " that begins the i-th string
      // on the line.  Only the first numberOfStrings elements
      // contain data.
    private int[] rightQuoteLocs = new int[1000];;
      // An array whose i-th element is the location of
      // (the left-side of) the " that ends the i-th string
      // on the line.  If that string runs to the end of the
      // line, then it equals endLineLoc.  Only the first 
      // numberOfStrings elements contain data.
    private int numberOfStrings;
      // the number of strings on the line. 
    
    // The definitions of the parentheses, the left parens are
    // in PARENS[0] .. PARENS[PCOUNT-1], and the right parens
    // are in PARENS[PCOUNT] ... PARENTS[2* PCOUNT -1]
    private static String[] PARENS  = {"(*", "<<", "(", "[", "{", "*)", ">>", ")", "]", "}"} ;
    private static int PCOUNT = 5;
    private static int COMMENT_BEGIN_IDX = 0;
    private static int LEFT_ROUND_PAREN_IDX = 2;
      // The index of "(" in PARENS
    
    // The three types of regions
    private static int MAIN_REGION = 0;
    private static int COMMENT_REGION = 1;
    private static int STRING_REGION = 2;
    
    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    
    /**
     * The method called when the user executes the Goto Matching Paren command.
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException {
        TLAEditor tlaEditor = EditorUtil.getTLAEditorWithFocus();
        document = tlaEditor.publicGetSourceViewer().getDocument();
        
        try {
            ITextSelection selection = (ITextSelection) tlaEditor
                    .getSelectionProvider().getSelection();
            Region selectedRegion = new Region(selection.getOffset(),
                    selection.getLength());
            
            int selectedParenIdx = getSelectedParen(selectedRegion);
            
            int lineNumber = selection.getStartLine();
              // Note: if the selection covers multiple lines, then 
              // selectParenIdx should have thrown an exception.
            if (lineNumber < 0) {
                throw new ParenErrorException("Toolbox bug: bad selected line computed", null);
            }
            
            setLineRegions(lineNumber);

//            try {
//                System.out.println("Current line: `" + 
//                   document.get(beginLineLoc, endLineLoc-beginLineLoc)+ "'");
//                for (int i = 0; i < numberOfStrings; i++) {
//                    System.out.println("String " + i +": " +
//                   document.get(leftQuoteLocs[i], rightQuoteLocs[i]-leftQuoteLocs[i]+1));
//                }
//                if (lineCommentLoc != endLineLoc) {
//                    System.out.println("End comment: `" +
//                   document.get(lineCommentLoc, endLineLoc - lineCommentLoc) + "'");
//                }
//            } catch (BadLocationException e) {
//                // TODO Auto-generated catch block
//                System.out.println("Exception printing line info");
//            }
            
        } catch (ParenErrorException e) {

            /*
             * Report the error.
             */
            IResource resource = ResourceHelper
                    .getResourceByModuleName(tlaEditor.getModuleName());
            ErrorMessageEraser listener = new ErrorMessageEraser(tlaEditor,
                    resource);
            tlaEditor.getViewer().getTextWidget().addCaretListener(listener);
            tlaEditor.getEditorSite().getActionBars().getStatusLineManager()
                    .setErrorMessage(e.message);
            Region region = e.region;

            if (region != null) {
                try {
                    // The following code was largely copied from the The
                    // ShowUsesHandler class.
                    IMarker marker = resource
                            .createMarker(PAREN_ERROR_MARKER_TYPE);
                    Map<String, Integer> markerAttributes = 
                            new HashMap<String, Integer>(2);
                    markerAttributes.put(IMarker.CHAR_START,
                            new Integer(region.getOffset()));
                    markerAttributes.put(IMarker.CHAR_END,
                                         new Integer(region.getOffset()
                                                      + region.getLength()));
                    marker.setAttributes(markerAttributes);
                    Spec spec = ToolboxHandle.getCurrentSpec();
                    spec.setMarkersToShow(null);
                    IMarker[] markersToShow = new IMarker[1];
                    markersToShow[0] = marker;
                    spec.setMarkersToShow(markersToShow);
                } catch (CoreException exc) {
                    System.out
                            .println("GotoMatchingParenHandler.execute threw CoreException");
                }
            }
        }
        return null;
    }

    /****************  The Subroutines *****************/
    
    /**
     * If location is the location in the document just to the right of a paren,
     * returns the index of the paren in PARENS.  Otherwise, it returns -1.
     * It should be called with location > 0; otherwise it always returns -1.
     * 
     * @param location
     * @return
     */
    private int getParenToLeftOf(int location) {
        for (int i = 0; i < PARENS.length; i++) {
            try {
                if (document.get(location - PARENS[i].length(), PARENS[i].length()).equals(PARENS[i])) {
                    return i;
                }
            } catch (BadLocationException e) {
                // this exception should occur only if location is close enough to
                // the beginning of the document so PARENS[i] couldn't fit to
                // the left of it, in which case we just want to do nothing here.
            }
        }
        return -1;
    }
    
    /**
     * Sets the region information for line number lineNumber--that is, it sets
     * 
     *    currLineNum, beginLineLoc, endLineLoc, lineCommentLoc, 
     *    leftQuoteLocs, rightQuoteLocs, and numberOfStrings.
     *    
     * @param lineNumber
     * @throws ParenErrorException
     */
    private void setLineRegions(int lineNumber) throws ParenErrorException {
        currLineNum = lineNumber;
        try {
            beginLineLoc = document.getLineOffset(lineNumber);
            endLineLoc = beginLineLoc + document.getLineLength(lineNumber);
            lineCommentLoc = endLineLoc;
            numberOfStrings = 0;
            boolean inString = false;
            for (int loc = beginLineLoc; loc < endLineLoc; loc++) {
                char ch = document.getChar(loc);
                if (inString) {
                    if (ch == '"') {
                        inString = false;
                        rightQuoteLocs[numberOfStrings - 1] = loc;
                    } 
                    else if (ch == '\\') {
                        loc++;
                    }
                } else {
                    if ( ch == '"') {
                        leftQuoteLocs[numberOfStrings] = loc;
                        numberOfStrings++;
                        inString = true;
                    } else {
                        if (ch == '\\' && loc + 1 < endLineLoc && document.getChar(loc+1) == '*') {
                            lineCommentLoc = loc ;
                            break ;
                        }
                    }
                }
            }
            if (inString) {
                rightQuoteLocs[numberOfStrings - 1] = endLineLoc;
            }
        } catch (BadLocationException e) {
            throw new ParenErrorException(
                    "Toolbox bug: BadLocationException in setLineRegions at line "
                            + lineNumber, null);
        }

        boolean inString = false;

    }
    
    /**
     * Sets currLoc, and returns the index of the selected paren in PARENS.  
     * If the region has zero length, then it selects the paren to its left and 
     * sets currLoc to the selection.  Otherwise, the region has to select a paren, 
     * and currLoc is set to the position to the right of that paren.
     * 
     * @param selectedRegion
     */
    private int getSelectedParen(Region selectedRegion)
            throws ParenErrorException {
        currLoc = selectedRegion.getOffset();
        if (selectedRegion.getLength() == 0) {
          int selectedParenIdx = getParenToLeftOf(currLoc);
          if (selectedParenIdx < 0) {
              throw new ParenErrorException("Paren not selected", null);
          }
          // Now test if we're between "(" and "*".
          if (    selectedParenIdx == LEFT_ROUND_PAREN_IDX 
               && getParenToLeftOf(currLoc+1) == COMMENT_BEGIN_IDX) {
              throw new ParenErrorException("Selection between  (  and  *", null);
          }
          return selectedParenIdx ;
        } else {
            String selection = null; // initialization to keep compiler happy.
            try {
                selection = document.get(selectedRegion.getOffset(),
                        selectedRegion.getLength());
            } catch (BadLocationException e) {
                // This should not happen
                System.out.println(
                   "BadLocationException in GotoMatchingParenHandler.getSelectedParen");
            }
            int selectedParenIdx = 0;
            boolean notDone = true ;
            while (notDone && (selectedParenIdx < PARENS.length)) {
                if (selection.equals(PARENS[selectedParenIdx])) {
                    notDone = false;
                } 
                else {
                    selectedParenIdx++;
                }
            }
            if (notDone) {
                throw new ParenErrorException("Selection is not a paren", null);
            }
            currLoc = currLoc + selectedRegion.getLength();
            return selectedParenIdx;
        }
    }
    
    /**
     * The exception thrown when a mismatched or unmatched paren or other problem
     * is found.
     */
    private static class ParenErrorException extends Exception  {
        /*
         * The message to be displayed in the status bar
         */
        String message;
        /*
         * The region containing the string to be highlighted, or null if none.
         */
        Region region;
        
        private ParenErrorException(String message, Region region){
             this.message = message;
            this.region = region;
        }
    }
    
    /**
     * An ErrorMessageEraser is a CaretListener that removes an error message and
     * Paren Error annotation.
     */
    private static class ErrorMessageEraser implements CaretListener{
        TLAEditor editor;
        IResource resource ;
        
       private ErrorMessageEraser(TLAEditor e, IResource res) {
            editor = e;
            resource = res;
        }

       public void caretMoved(CaretEvent event) {
           // TODO Auto-generated method stub
           editor.getEditorSite().getActionBars().getStatusLineManager().setErrorMessage(
                   null);
           editor.getViewer().getTextWidget().removeCaretListener(this);
           try {
            resource.deleteMarkers(PAREN_ERROR_MARKER_TYPE, false, 99);
        } catch (CoreException e) {
            // TODO Auto-generated catch block
            System.out.println("caretMoved threw exception");
        }

       } 
    }
    
}
