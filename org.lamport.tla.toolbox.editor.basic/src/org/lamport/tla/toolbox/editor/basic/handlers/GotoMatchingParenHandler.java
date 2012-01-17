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
 * right of the matching paren, except in case of error.  (It also does that if
 * the cursor is between the two charecters of a two-character paren.) 
 * If there is an error, then the cursor is not moved, an error message 
 * is put in the Toolbox's status bar (at the bottom of the window), and if 
 * the error is unmatched pair of parens, the parens are highlighted with
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
 * Matching considers only parens that appear in the same region as the selected paren.
 *  
 * There is one problematic case: when the cursor is between the '(' and the '*' in
 * "(*".  In that case, the cursor is considered not to be at a paren.
 * 
 * Note that text outside the module is treated the same as if it were in the module.
 * I don't know anything better to do for matching parens before or after the module.
 * While it might be better to consider text before or after the module to be
 * in separate regions than module text, it doesn't seem to be worth the trouble.
 * The user will see easily enough if a paren outside the module matches one inside 
 * the module.  
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
    private int currLineNum ;  
      // the number of the line (Java numbering)
    private int beginCurrRegion;
    private int endCurrRegion;
      // These are the beginning and end of the search
      // region containing currLoc--that is the offset
      // of the first character in the region and the
      // offset of the character immediately after the region.
      // If there are no strings on the line and we are searching
      // the main region, then these fields equal beginLineLoc
      // and endlineLoc.
    private int currRegionNumber;
      // - If regionType = STRING_REGION, then this is the
      // number of the string on the line (Java numbering).
      // That is, leftQuoteLocs[currRegionNumber] and
      // rightQuoteLocs[currRegionNumber] delimit the
      // current region.  
      //
      // - If regionType = MAIN_REGION, then
      // the current region lies between string number 
      // currRegionNumber-1 and string number currRegionNumber.
      // (If there are no strings, then currRegionNumber = 0,
      // and if the current region lies to the right of the last 
      // string on the line, then currRegionNumber equals the
      // number of strings.
      //
      // - If regionType = COMMENT_REGION, then this
      //   field is not meaningful.
    
    private int beginLineLoc ;
      // the offset of the beginning of the current line
    private int endLineLoc ;
      // the offset of the end of the current line, which
      // is the same as that of the beginning of the next
      // line, except at the end of the document.
    private int lineCommentLoc;
      // if there is an end-of-line comment, this is
      // the offset of the beginning of the "\*";
      // otherwise, it equals endLineLoc
    private int[] leftQuoteLocs = new int[1000];
      // An array whose i-th element is the location of
      // (immediately to the left of)  the " that begins the i-th string
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
    // Left paren PARENS[i] matches PARENS[i + PCOUNT], and parens
    // with indices i and j are matching iff (i - j) % PCOUNT equals 0.
    private static String[] PARENS  = 
              {"(*", "<<", "(", "[", "{", "*)", ">>", ")", "]", "}"} ;
    private static int PCOUNT = 5;
    private static int COMMENT_BEGIN_IDX = 0;
    private static int LEFT_ROUND_PAREN_IDX = 2;
      // The index of "(" in PARENS
    private static int BEGIN_MULTILINE_COMMENT_IDX = 0;
      // The index of "(*" in PARENS.
    
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
                throw new ParenErrorException("Toolbox bug: bad selected line computed", null, null);
            }
            
            setLineRegions(lineNumber);
            setRegionInfo();
            
            if (selectedParenIdx < PCOUNT) {
                findMatchingRightParen(selectedParenIdx);
            } 
            else {
                findMatchingLeftParen(selectedParenIdx);
            }
            tlaEditor.selectAndReveal(currLoc, 0);            
        } catch (ParenErrorException e) {
            /*
             * Report the error.
             */
            IResource resource = ResourceHelper
                    .getResourceByModuleName(tlaEditor.getModuleName());
            ErrorMessageEraser listener = new ErrorMessageEraser(tlaEditor,
                    resource);
            tlaEditor.getViewer().getTextWidget().addCaretListener(listener);
            tlaEditor.getEditorSite().getActionBars().getStatusLineManager().setErrorMessage(e.message);
            
            Region[] regions = e.regions;
            if (regions[0] != null) {
                try {
                    // The following code was largely copied from the The
                    // ShowUsesHandler class.
                    Spec spec = ToolboxHandle.getCurrentSpec();
                    spec.setMarkersToShow(null);
                    IMarker[] markersToShow = new IMarker[2];
                    for (int i = 0; i < 2; i++) {
                        IMarker marker = resource
                                .createMarker(PAREN_ERROR_MARKER_TYPE);
                        Map<String, Integer> markerAttributes = new HashMap<String, Integer>(
                                2);
                        markerAttributes.put(IMarker.CHAR_START, new Integer(
                                regions[i].getOffset()));
                        markerAttributes.put(
                                IMarker.CHAR_END,
                                new Integer(regions[i].getOffset()
                                        + regions[i].getLength()));
                        marker.setAttributes(markerAttributes);

                        markersToShow[i] = marker;
                    }
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
     * Assumes that currLoc is just past a left paren with index
     * parenIdx in PARENS.  It sets currLoc to the location just past
     * the matching right paren, or throws an exception if there is 
     * a matching error.
     * 
     * @param parenIdx
     */
    private void findMatchingRightParen(int parenIdx) throws ParenErrorException {
        int savedCurrLoc = currLoc;
        while (true) {
            currLoc++;
            int pidx = -1;
            while (currLoc <= endCurrRegion  && ((pidx = getParenToLeftOf(currLoc)) == -1)) {
               currLoc++;
            }
            if (pidx == -1) {
                getNextRegion();
                currLoc = beginCurrRegion;
            }
            else {
                /*
                 * Need to check if we're just past the '(' in "(*".  Because of the
                 * unlikely event that the '(' is the last character in the file,
                 * it's easier to check that by calling getParenToLeftOf.
                 * 
                 */
                if (pidx == LEFT_ROUND_PAREN_IDX && 
                      getParenToLeftOf(currLoc+1) == BEGIN_MULTILINE_COMMENT_IDX) {
                    currLoc++;
                    pidx = BEGIN_MULTILINE_COMMENT_IDX;
                }
                if (pidx < PCOUNT) {
                    // This is a left paren
                    findMatchingRightParen(pidx);
                }
                else {
                    // This is a right paren
                    if ((pidx - parenIdx) % PCOUNT == 0 ) {
                        return;
                    }
                    else {
                        // Mismatched paren
                        throw new ParenErrorException(PARENS[parenIdx] + " matched by " + PARENS[pidx] , 
                           new Region(currLoc - PARENS[pidx].length(), PARENS[pidx].length()),
                           new Region(savedCurrLoc - PARENS[parenIdx].length(), PARENS[parenIdx].length()));
                    }
                }
            }
        }
    }
    
    /**
     * Assumes that currLoc is just past a right paren with index
     * parenIdx in PARENS.  It sets currLoc to the location just past
     * the matching left paren, or throws an exception if there is 
     * a matching error.
     * 
     * @param parenIdx
     */
    private void findMatchingLeftParen(int parenIdx) throws ParenErrorException {
        int savedCurrLoc = currLoc;
        
        /*
         * justWentToPrevRegion is true iff the search just moved to the end
         * of a new region.
         * 
         * When control is at the beginning of the while loop and justWentToPrevRegion
         * is false, there is a paren to the left of currLoc that must be skipped over 
         * when searching for the mathing left paren.  The paren with index 
         * lastParenSearched in PARENS is the right paren that either is the paren 
         * to be skipped over or else the right paren that matches the paren to be 
         * skipped over. 
         */
        int lastParenSearched = parenIdx;
        boolean justWentToPrevRegion = false;
        while (true) {
            if (! justWentToPrevRegion) {
                currLoc = currLoc - PARENS[lastParenSearched].length();
            }
            int pidx = -1;
            while (currLoc > beginCurrRegion  && ((pidx = getParenToLeftOf(currLoc)) == -1)) {
               currLoc--;
            }
            if (pidx == -1) {
                getPrevRegion();
                currLoc = endCurrRegion;
                justWentToPrevRegion = true;
            }
            else {
                if (pidx >= PCOUNT) {
                    // This is a right paren
                    findMatchingLeftParen(pidx);
                    lastParenSearched = pidx;
                    justWentToPrevRegion = false;
                }
                else {
                    // This is a left paren
                    if ((pidx - parenIdx) % PCOUNT == 0 ) {
                        return;
                    }
                    else {
                        // Mismatched paren
                        throw new ParenErrorException(PARENS[pidx] + " matches " +  PARENS[parenIdx], 
                           new Region(currLoc - PARENS[pidx].length(), PARENS[pidx].length()),
                           new Region(savedCurrLoc - PARENS[parenIdx].length(), PARENS[parenIdx].length()));
                    }
                }
            }
        }
    }
    
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
     * Throws "Unmatched paren" exception if document does not have line lineNumber.
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
            throw new ParenErrorException("Unmatched paren", null, null);
//            throw new ParenErrorException(
//                    "Toolbox bug: BadLocationException in setLineRegions at line "
//                            + lineNumber, null);
        }
    }
    
    /**
     * Sets regionType, beginCurrRegion, and endCurrRegion.  It assumes that
     * setLineRegions has been called, and uses that and currLoc to determine
     * the region type and current region.
     */
    private void setRegionInfo() {
        currRegionNumber = 0;
        beginCurrRegion = beginLineLoc;
        endCurrRegion = endLineLoc;
        regionType = MAIN_REGION;
        boolean notDone = true ;
        while (notDone && currRegionNumber < numberOfStrings) {
            if (currLoc <= leftQuoteLocs[currRegionNumber]) {
                notDone = false;
                endCurrRegion = leftQuoteLocs[currRegionNumber];
            }
            else if (currLoc <= rightQuoteLocs[currRegionNumber]) {
                notDone = false;
                regionType = STRING_REGION;
                beginCurrRegion = leftQuoteLocs[currRegionNumber] + 1;
                endCurrRegion = rightQuoteLocs[currRegionNumber];
            } 
            else {
                beginCurrRegion = rightQuoteLocs[currRegionNumber] + 1;
                currRegionNumber++;
            }
        }
        if (notDone || numberOfStrings == 0) {
            if (lineCommentLoc < currLoc) {
                regionType = COMMENT_REGION;
                beginCurrRegion = lineCommentLoc + 2; 
                  // Note: 2 must be changed in the unlikely event that we
                  // either have a 1-character end-of-line comment token
                  // or we have one with more than 2 tokens that contains a
                  // paren.
            } 
            else {
                endCurrRegion = lineCommentLoc;
            }
        }
    }
    
    /**
     * Sets beginCurrRegion, endCurrRegion, and (perhaps) currRegionNumber
     * to indicate the next region of type regionType.  If that region is
     * on a later line, it will also call setLineLineRegions.  If there
     * is no next region of this type (because it runs off the end of the
     * file looking for one), it throws an "Unmatched paren" error.
     *    
     * @throws ParenErrorException
     */
    private void getNextRegion() throws ParenErrorException {
        if (regionType == MAIN_REGION) {
            if (currRegionNumber < numberOfStrings) {
                beginCurrRegion = rightQuoteLocs[currRegionNumber] + 1;
                currRegionNumber++;
                if (currRegionNumber == numberOfStrings) {
                    endCurrRegion = lineCommentLoc;
                } else {
                    endCurrRegion = leftQuoteLocs[currRegionNumber];
                }
            } else {
                setLineRegions(currLineNum + 1);
                currRegionNumber = 0;
                beginCurrRegion = beginLineLoc;
                if (numberOfStrings == 0) {
                    endCurrRegion = lineCommentLoc;
                } 
                else {
                    endCurrRegion = leftQuoteLocs[0];
                }
            }
        }
        else if (regionType == STRING_REGION) {
            if (currRegionNumber < numberOfStrings - 1) {
                currRegionNumber++;
            } else {
                setLineRegions(currLineNum + 1);
                while (numberOfStrings == 0) {
                    setLineRegions(currLineNum + 1);
                }
                currRegionNumber = 0;
            }
            beginCurrRegion = leftQuoteLocs[currRegionNumber] + 1;
            endCurrRegion = rightQuoteLocs[currRegionNumber];
        }
        else {
         // regionType == COMMENT_REGION
            setLineRegions(currLineNum + 1);
            while (lineCommentLoc == endLineLoc) {
                setLineRegions(currLineNum + 1);
            }
            beginCurrRegion = lineCommentLoc + 2;
            endCurrRegion = endLineLoc;
        }
    }
    
    /**
     * Sets beginCurrRegion, endCurrRegion, and (perhaps) currRegionNumber
     * to indicate the previous region of type regionType.  If that region is
     * on a later line, it will also call setLineLineRegions.  If there
     * is no previous region of this type (because it runs off the end of the
     * file looking for one), it throws an "Unmatched paren" error.
     *    
     * @throws ParenErrorException
     */
    private void getPrevRegion() throws ParenErrorException {
        if (regionType == MAIN_REGION) {
            if (currRegionNumber  > 0) {
                currRegionNumber--;
                endCurrRegion = leftQuoteLocs[currRegionNumber];
                
                if (currRegionNumber == 0) {
                    beginCurrRegion = beginLineLoc;
                } else {
                    beginCurrRegion = rightQuoteLocs[currRegionNumber-1] + 1;
                }
            } else {
                setLineRegions(currLineNum - 1);
                currRegionNumber = numberOfStrings;
                endCurrRegion = lineCommentLoc;
                if (numberOfStrings == 0) {
                    beginCurrRegion = beginLineLoc;
                } 
                else {
                    beginCurrRegion = rightQuoteLocs[numberOfStrings-1] + 1;
                }
            }
        }
        else if (regionType == STRING_REGION) {
            if (currRegionNumber > 0) {
                currRegionNumber--;
            } else {
                setLineRegions(currLineNum - 1);
                while (numberOfStrings == 0) {
                    setLineRegions(currLineNum - 1);
                }
                currRegionNumber = numberOfStrings - 1;
            }
            beginCurrRegion = leftQuoteLocs[currRegionNumber] + 1;
            endCurrRegion = rightQuoteLocs[currRegionNumber];
        }
        else {
         // regionType == COMMENT_REGION
            setLineRegions(currLineNum - 1);
            while (lineCommentLoc == endLineLoc) {
                setLineRegions(currLineNum - 1);
            }
            beginCurrRegion = lineCommentLoc + 2;
            endCurrRegion = endLineLoc;
        }
    }
    
    /**
     * Sets currLoc, and returns the index of the selected paren in PARENS.  
     * If the region has zero length, then it selects the paren to its left and 
     * sets currLoc to the selection--or the 2-char paren it's in the
     * middle of.  Otherwise, the region has to select a paren, 
     * and currLoc is set to the position to the right of that paren.
     * 
     * @param selectedRegion
     */
    private int getSelectedParen(Region selectedRegion)
            throws ParenErrorException {
        currLoc = selectedRegion.getOffset();
        int selectedParenIdx;
        if (selectedRegion.getLength() == 0) {
          selectedParenIdx = getParenToLeftOf(currLoc);
          if (selectedParenIdx == -1) {
              int tryNext = getParenToLeftOf(currLoc + 1);
              if (tryNext == -1 || PARENS[tryNext].length() == 1) {
                throw new ParenErrorException("Paren not selected", null, null);
              }
              currLoc++;
              return tryNext;
          }       
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
            selectedParenIdx = 0;
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
                throw new ParenErrorException("Selection is not a paren", null, null);
            }
            currLoc = currLoc + selectedRegion.getLength();
        }
        
        // Now test if we're between "(" and "*".
        if (    selectedParenIdx == LEFT_ROUND_PAREN_IDX
             && getParenToLeftOf(currLoc + 1) == COMMENT_BEGIN_IDX) {
//            throw new ParenErrorException("Selection between  (  and  *", null);
            currLoc++;
            return BEGIN_MULTILINE_COMMENT_IDX;
        }
        return selectedParenIdx ;
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
        Region[] regions = new Region[2];
        
        private ParenErrorException(String message, Region region1, Region region2){
             this.message = message;
             this.regions[0] = region1;
             this.regions[1] = region2;
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
