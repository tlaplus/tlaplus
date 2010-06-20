import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.ide.undo.CreateMarkersOperation;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil.StringAndLocation;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;
import util.UniqueString;

/**
 * 
 */

/**
 * @author lamport
 *
 */
public class ShowUsesHandler extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // TODO Auto-generated method stub
        System.out.println("ShowUsesHandler.execute called");
        
        // Get the token currently being pointed at.
        // The following code was copied from TLAHyperlinkDetector.detectHyperlinks
        // and from the code in TLAEditor$OpenDeclarationHandler.execute
        // that calls it.
        
        // First, we get the arguments we need for EditorUtil.getTokenAt
        TLAEditorAndPDFViewer editor = (TLAEditorAndPDFViewer) HandlerUtil.getActiveEditor(event);
        ISourceViewer internalSourceViewer = editor.getTLAEditor().publicGetSourceViewer();
        IDocument document = internalSourceViewer.getDocument();
        
        ITextSelection selection = (ITextSelection) editor.getTLAEditor().getSelectionProvider().getSelection();
        IRegion region = new Region(selection.getOffset(), selection.getLength());
        
        // We now try to get the label (the name of the symbol we are looking for)
        // from EditorUtil.getTokenAt
        StringAndLocation goodLabelAndLoc = EditorUtil.getTokenAt(document, region.getOffset(), region.getLength());
        String label = null; 
        Location location = null;
        
        // If we failed to get the token, it could be because the editor
        // is dirty.  In that case, we use Simon's code to get it directly
        // from the document.
        if (goodLabelAndLoc == null) {
            if (region.getLength() == 0)
            {
                region = DocumentHelper.getRegionExpandedBoth(document, region.getOffset(), DocumentHelper
                        .getDefaultWordDetector());
                location = EditorUtil.getLocationAt(document, region.getOffset(), region.getLength());
            }
            try
            {
                label = document.get(region.getOffset(), region.getLength());
            } catch (BadLocationException e)
            {
               // nothing to do but quit
            }
  
        } else {
            label = goodLabelAndLoc.string;
            location = goodLabelAndLoc.location;
        }
        if (label == null) {
            return null;
        }
        System.out.println("We are searching for `" + label + "'");
        
        TLAEditor tlaEditor = EditorUtil.getTLAEditorWithFocus();
        if (tlaEditor == null) {
            return null;
        }
        String moduleName = tlaEditor.getModuleName();
        ModuleNode moduleNode = ResourceHelper.getModuleNode(moduleName);
        if (moduleNode == null) {
            return null;
        }
        SymbolNode resolvedSymbol = EditorUtil.lookupOriginalSymbol(UniqueString.uniqueStringOf(label), moduleNode,
                location, null);
        if (resolvedSymbol == null) {
            return null;
        }
        System.out.println("We found symbol node named " + resolvedSymbol.getName());
        
        OpApplNode[] uses = ResourceHelper.getUsesOfSymbol(resolvedSymbol, moduleNode);
        
        for (int i=0; i < uses.length; i++) {
            System.out.println("Node " + i + "has uid " + uses[i].getUid());
        }
        System.out.println("Number of uses found: " + uses.length);
        
        IFile ifile = ((FileEditorInput) tlaEditor.getEditorInput()).getFile();
        System.out.println("Resource path: " + ifile.getFullPath().toString());
        IResource resource = ifile; 
        try
        {
            System.out.println("Starting marker code;");
            IMarker marker = resource.createMarker("org.lamport.tla.toolbox.editor.basic.showUse");
            Map markerAttributes = new HashMap(2);
            markerAttributes.put(IMarker.CHAR_START, new Integer(0));
            markerAttributes.put(IMarker.CHAR_END, new Integer(50));
            marker.setAttributes(markerAttributes);
            System.out.println("Ending marker code;");
            

        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            System.out.println("Exception thrown by marker code;");
        }
        //
        //
        // Compute locations of the uses.  Must look at the OpApplNode's syntax node tree
        // and check for the following cases:
        //   Foo(...) : the node is an N_OpApplication node, it's
        //              first child is an N_GeneralID whose location is good.
        //   ... %% ... : the node is an N_InfixExpr node, whose 2nd child is
        //                an N_GenInfixOp whose location is good.
        //   x : the node is an N_GeneralID node whose location is good
        //   ...^+ : the node is an N_PostfixExpr node whose second heir
        //           is an N_GeneralPostfixOp whose location is good
        return null;
    }

}
