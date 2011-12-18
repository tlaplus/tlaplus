/**
 *  Note: I attached this command to F10 because the F9 key on my ancient
 *  home keyboard doesn't work.  It should probably go on F9 when I'm through
 *  working on the TLA to PlusCal mapping.
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.commands.IHandlerListener;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.ISourceViewer;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;

import pcal.MappingObject;
import pcal.TLAtoPCalMapping;

/**
 * @author lamport
 *
 */
public class GotoPCalSourceHandler extends AbstractHandler implements IHandler {


    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException {
        
        // Set mapping to the TLAtoPCalMapping.
        // To do that, we first get the current spec .
        Spec spec = ToolboxHandle.getCurrentSpec();
        if (spec == null)
        {
            return null;
        }

        // We need the module name for looking up the TLAtoPCalMapping.
        // We get the module name from the current editor.
        TLAEditor tlaEditor = EditorUtil.getTLAEditorWithFocus();
        if (tlaEditor == null)
        {
            return null;
        }
        String moduleName = tlaEditor.getModuleName();
       
        TLAtoPCalMapping mapping = spec.getTpMapping(moduleName + ".tla");
        
        /*
         * If mapping is null, then the last translation failed so 
         * we do nothing.
         */
        if (mapping == null) {
            return null;
        }
        MappingObject[][] map = mapping.mapping;
        
        // The following code copied with modifications from GotoNextUseHandler
        // begin copy
        ISourceViewer internalSourceViewer = tlaEditor.publicGetSourceViewer();
        IDocument document = internalSourceViewer.getDocument();
        ITextSelection selection = (ITextSelection) tlaEditor.getSelectionProvider().getSelection();
        IRegion region = new Region(selection.getOffset(), selection.getLength());


        // Sets currentLine to the line of text of the module containing the beginning of the
        // current region, and sets currentPos to the position of the beginning of the
        // current region in that line. The Document.getLineLength method seems to include
        // the length of the line's delimeter, which should not be included in currentLine.
        String currentLine;
        int currentPos;
        int offsetOfLine;
        try
        {
            int lineNumber = document.getLineOfOffset(region.getOffset());
            int lineDelimLength = 0;
            String delim = document.getLineDelimiter(lineNumber);
            if (delim != null)
            {
                lineDelimLength = delim.length();
            }
            ;
            offsetOfLine = document.getLineOffset(lineNumber);
            currentLine = document.get(offsetOfLine, document.getLineLength(lineNumber) - lineDelimLength);
            currentPos = region.getOffset() - offsetOfLine;
        } catch (BadLocationException e)
        {
            System.out.println("Exception thrown");
            return null;
        }
        // end copy
XXXXXXXX editing here
        tlaEditor.selectAndReveal(0, 22);
// For testing
MappingObject.printMapping(map);
        return null;
    }

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#isEnabled()
     */
    public boolean isEnabled() {
        Spec spec = ToolboxHandle.getCurrentSpec();
        if (spec == null)
        {
            return false;
        }
        TLAEditor tlaEditor = EditorUtil.getTLAEditorWithFocus();
        if (tlaEditor == null)
        {
            return false;
        }
        String moduleName = tlaEditor.getModuleName();
       
       return spec.getTpMapping(moduleName + ".tla") != null; 
    }

}
