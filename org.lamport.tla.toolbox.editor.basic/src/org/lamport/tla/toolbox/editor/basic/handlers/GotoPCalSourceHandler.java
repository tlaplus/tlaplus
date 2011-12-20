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
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.ISourceViewer;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.UIHelper;

import pcal.MappingObject;
import pcal.PCalLocation;
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
         * we do nothing. This should be impossible, since the command should
         * not be enabled.
         */
        if (mapping == null) {
            return null;
        }
        MappingObject[][] map = mapping.mapping;
        
        
        /*
         * The following code finds the line and column numbers of the beginning and
         * end of the selected region.  The code for getting that information was
         * copied from GotoNextUseHandler.
         */
        ISourceViewer internalSourceViewer = tlaEditor.publicGetSourceViewer();
        IDocument document = internalSourceViewer.getDocument();
        ITextSelection selection = (ITextSelection) tlaEditor.getSelectionProvider().getSelection();
        int selectionOffset = selection.getOffset();
        int selectionLength = selection.getLength();

        int selectionBeginLine;
        int selectionBeginCol;
        int selectionEndLine;
        int selectionEndCol;
        try
        {
            selectionBeginLine = document.getLineOfOffset(selectionOffset);
            int offsetOfLine = document.getLineOffset(selectionBeginLine);
            selectionBeginCol = selectionOffset - offsetOfLine;
            selectionEndLine = document.getLineOfOffset(selectionOffset + selectionLength);
            offsetOfLine = document.getLineOffset(selectionEndLine);
            selectionEndCol = selectionOffset + selectionLength - offsetOfLine;
        } catch (BadLocationException e)
        {
            System.out.println("Exception thrown in GotoPCalSourceHandler");
            return null;
        }
        
        /*
         * Set newStartOfTranslation to be the best guess of the line number in the
         * current contents of the editor that corresponds to what was line
         * mapping.tlaStartLine when the algorithm was translated. 
         * It is computed by assuming that neither the algorithm nor the translation
         * have changed, but they both may have been moved down by the same 
         * number delta of lines (possibly negative).  A more sophisticated approach 
         * using fingerprints of lines could be used, requiring that the necessary 
         * fingerprint information be put in TLAtoPCalMapping.
         */
        int beginAlgorithmLine = DocumentHelper.GetLineOfPCalAlgorithm(document);
        if (beginAlgorithmLine == -1) {
            MessageDialog.openWarning(UIHelper.getShellProvider().getShell(), "Cannot find algorithm",
                    "The algorithm is no longer in the module.");
            return null ;
        }       
        int delta = beginAlgorithmLine - mapping.algLine ;
        int newStartOfTranslation = mapping.tlaStartLine + delta;

        /*
         * Call TLAtoPCalMapping.ApplyMapping to find the PCal source, using
         * the region tlaRegion obtained by adjusting the line numberss of the selected 
         * region to be relative to newStartOfTranslation.
         */
        pcal.Region tlaRegion = 
             new pcal.Region(new PCalLocation(selectionBeginLine - newStartOfTranslation,
                                              selectionBeginCol),
                             new PCalLocation(selectionEndLine - newStartOfTranslation,
                                              selectionEndCol));

        pcal.Region sourceRegion = 
               TLAtoPCalMapping.ApplyMapping(mapping, tlaRegion);
        if (sourceRegion == null) {
            return null;
        }
        
        try {
            int sourceStartLoc = 
                    document.getLineOffset(sourceRegion.getBegin().getLine() + delta) 
                      + sourceRegion.getBegin().getColumn();
            int sourceEndLoc = 
                    document.getLineOffset(sourceRegion.getEnd().getLine() + delta) 
                    + sourceRegion.getEnd().getColumn();
            
            /*
             * The following command makes executing ReturnFromOpenDecl (F4) return
             *  to the selected location.
             */
            EditorUtil.setReturnFromOpenDecl();
            
            tlaEditor.selectAndReveal(sourceStartLoc, sourceEndLoc - sourceStartLoc);
                    
        } catch (BadLocationException e) {
            System.out.println("Bad Location for source region.");
            e.printStackTrace();
            return null;
        }
        return null;
    }

    /** 
     * We disable the command if there is no translation mapping.
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
