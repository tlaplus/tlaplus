package org.lamport.tla.toolbox.editor.basic.handlers;
import java.util.Arrays;
import java.util.Comparator;
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
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.ide.undo.CreateMarkersOperation;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil.StringAndLocation;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;
import tla2sany.st.SyntaxTreeConstants;
import util.UniqueString;

/**
 * 
 */

/**
 * This is the handler for the Show Uses command, which allows the user
 * to mark and visit all uses of a symbol.  However, unlike the Show
 * Declaration command, for an instantiated symbol like Foo!bar, it 
 * shows only uses of Foo!bar, not other uses of the original symbol
 * bar.
 * 
 * If the chosen symbol is used in more than one module (possible only
 * by EXTENDing a module with its declaration or by INSTANCEing it
 * with no renaming or parameter substitution), then a pop-up dialog
 * allows the user to choose which module to display.
 * 
 * Note: Implementing SyntaxTreeConstants simply imports the definitions
 *       of the constants defined in that interface.
 * 
 * @author lamport
 *
 */
public class ShowUsesHandler extends AbstractHandler implements IHandler, SyntaxTreeConstants
{
    /**    This is the handler for the Goto Next Use command.
     * 
     * @author lamport
     *
     */
    public class DontGotoNextUseHandler extends AbstractHandler implements IHandler
    {

        /* (non-Javadoc)
         * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
         */
        public Object execute(ExecutionEvent event) throws ExecutionException
        {
           System.out.println("Execute Goto Next");
            
            // TODO Auto-generated method stub
            return null;
        }
       public boolean isEnabled() {
           Spec spec = ToolboxHandle.getCurrentSpec();
           if (spec == null) {
               return false;
           }
           return spec.getMarkersToShow() != null; 
       }
    }

    public static final String SHOW_USE_MARKER_TYPE = "org.lamport.tla.toolbox.editor.basic.showUse";

    
    private String test = "This is a test";

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {

        test = "This was reset by Show Uses";
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
        // is dirty. In that case, we use Simon's code to get it directly
        // from the document.
        if (goodLabelAndLoc == null)
        {
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
                return null;
            }

        } else
        {
            label = goodLabelAndLoc.string;
            location = goodLabelAndLoc.location;
        }
        if (label == null || location == null)
        {
            return null;
        }
        System.out.println("We are searching for `" + label + "'");

        TLAEditor tlaEditor = EditorUtil.getTLAEditorWithFocus();
        if (tlaEditor == null)
        {
            return null;
        }
        String moduleName = tlaEditor.getModuleName();
        ModuleNode moduleNode = ResourceHelper.getModuleNode(moduleName);
        if (moduleNode == null)
        {
            return null;
        }
        SymbolNode resolvedSymbol = EditorUtil.lookupSymbol(UniqueString.uniqueStringOf(label), moduleNode, location,
                null);
        if (resolvedSymbol == null)
        {
            return null;
        }
        System.out.println("We found symbol node named " + resolvedSymbol.getName());

        // Set tempModuleNames to the sorted array of all user module names.
        String[] tempModuleNames = ResourceHelper.getModuleNames();
        for (int k = 0; k < tempModuleNames.length; k++)
        {
            System.out.println("tempModuleName[" + k + "] = " + tempModuleNames[k]);
        }

        // Set tempUsesArray[i] to the array of OpAplNode[] nodes at are uses of
        // resolvedSymbol in module moduleNames[i], and sets numberOfModulesUsedIn
        // to the number of values of i for which usesArray[i] is neither null
        // nor a zero-length array.
        int numberOfModulesUsedIn = 0;
        OpApplNode[][] tempUsesArray = new OpApplNode[tempModuleNames.length][];
        for (int i = 0; i < tempModuleNames.length; i++)
        {
            tempUsesArray[i] = ResourceHelper.getUsesOfSymbol(resolvedSymbol, ResourceHelper
                    .getModuleNode(tempModuleNames[i]));
            if ((tempUsesArray[i] != null) && (tempUsesArray[i].length > 0))
            {
                numberOfModulesUsedIn++;
            }
            for (int k = 0; k < tempUsesArray[i].length; k++)
            {
                System.out.println("tempUsesArray[" + i + "][" + k + "] = "
                        + tempUsesArray[i][k].getLocation().toString());
            }
        }

        // Raise an error menu if there are no instances.
        if (numberOfModulesUsedIn == 0)
        {
            MessageDialog.openWarning(UIHelper.getShellProvider().getShell(), "Cannot find uses",
                    "There are no uses of the symbol " + resolvedSymbol.getName());
            return null;
        }

        // Set usesArray and moduleNames to the subarrays of of tempUsesArray and
        // tempModuleNames for which there are instances of the symbols, with the
        // currently selected module's name put first if it is one of them.
        OpApplNode[][] usesArray = new OpApplNode[numberOfModulesUsedIn][];
        String[] moduleNames = new String[numberOfModulesUsedIn];
        int j = 0;
        for (int i = 0; i < tempModuleNames.length; i++)
        {
            if ((tempUsesArray[i] != null) && (tempUsesArray[i].length > 0))
            {
                usesArray[j] = tempUsesArray[i];
                moduleNames[j] = tempModuleNames[i];
                j++;
            }
        }
        j = -1;
        for (int i = 0; i < moduleNames.length; i++)
        {
            if (moduleName.equals(moduleNames[i]))
            {
                j = i;
                break;
            }
        }
        if (j > 0)
        {
            OpApplNode[] savedUses = usesArray[j];
            for (int i = j - 1; i > -1; i--)
            {
                usesArray[i + 1] = usesArray[i];
                moduleNames[i + 1] = moduleNames[i];
            }
            usesArray[0] = savedUses;
            moduleNames[0] = moduleName;
        }
        
        // We need the current spec for setting the fields
        // that the Goto Next/Previous Use commands need.
        Spec spec = ToolboxHandle.getCurrentSpec();
        
        // If there are uses in more than one module, have the user choose
        // which one
        String moduleToShow = null;
         if (moduleNames.length > 1)
        {
            // TODO: add the code to select which module to show.
            moduleToShow = moduleName;
        } else
        {
            moduleToShow = moduleName;
        }
        spec.setModuleToShow(moduleToShow);
         
        int moduleIndex = -1;
        for (int i = 0; i < moduleNames.length; i++)
        {
            if (moduleNames[i].equals(moduleToShow))
            {
                moduleIndex = i;
                break;
            }
        }
        if (moduleIndex < 0)
        {
            Activator.logDebug("Could not find module name in array in which it should be." + "This is a bug.");
            return null;
        }

        // Set locations to the array of Locations of the uses. To do this, we
        // look at the OpApplNode's syntax node tree and check for the following cases:
        // Foo(...) : the node is an N_OpApplication node, it's
        // first child is an N_GeneralID whose location is good.
        // ... %% ... : the node is an N_InfixExpr node, whose 2nd child is
        // an N_GenInfixOp whose location is good.
        // x : the node is an N_GeneralID node whose location is good
        // ...^+ : the node is an N_PostfixExpr node whose second heir
        // is an N_GeneralPostfixOp whose location is good
        OpApplNode[] uses = usesArray[moduleIndex];
        Location[] locations = new Location[uses.length];
        for (int i = 0; i < locations.length; i++)
        {
            // Set stn to the syntax tree node whose location should
            // be used.
            SyntaxTreeNode stn = (SyntaxTreeNode) uses[i].stn;
            switch (stn.getKind()) {
            case N_OpApplication:
                stn = (SyntaxTreeNode) stn.heirs()[0];
                break;
            case N_InfixExpr:
            case N_PostfixExpr:
                stn = (SyntaxTreeNode) stn.heirs()[1];
                break;
            default:
                System.out.println("Found unexpected kind " + stn.getKind() + " for stn node of symbol use.");
            }
            locations[i] = stn.getLocation();
        }
        Arrays.sort(locations, new LocationComparator());

        // Jump to the first location. This ensures that the module is
        // now displayed by the current editor. (At least, I hope this
        // happens synchronously.)
        UIHelper.jumpToLocation(locations[0]);
        spec.setCurrentSelection(0);

        // Get the resource on which markers are to go, and set the markers.
        IResource resource = ResourceHelper.getResourceByModuleName(spec.getModuleToShow());
        
        if (resource == null) {
            System.out.println("Why the hell is the resource null?");
            return null;
        }
        
        try
        {
            // Remove all markers showing uses.
            resource.deleteMarkers(SHOW_USE_MARKER_TYPE, false, 99);
            spec.setMarkersToShow(null);
            
            IMarker[] markersToShow = new IMarker[locations.length];
            
            // create the markers and put them in this.markersToShow
            for (int i = 0; i < markersToShow.length; i++)
            {
                // The following is inefficient, because it's doing the same
                // computation each time to find the document from the
                // location.
                IRegion iregion = AdapterFactory.locationToRegion(locations[i]);
                IMarker marker;
                marker = resource.createMarker(SHOW_USE_MARKER_TYPE);
                Map markerAttributes = new HashMap(2);
                markerAttributes.put(IMarker.CHAR_START, new Integer(iregion.getOffset()));
                markerAttributes.put(IMarker.CHAR_END, new Integer(iregion.getOffset() + iregion.getLength()));
                marker.setAttributes(markerAttributes);
                markersToShow[i] = marker;
            }
            spec.setMarkersToShow(markersToShow);

        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

        // System.out.println("Modules with uses:");
        // for (int i = 0; i < moduleNames.length; i++)
        // {
        // System.out.println(moduleNames[i]);
        // }
        // ResourceHelper.getUsesOfSymbol(resolvedSymbol, moduleNode);

        // System.out.println("Resource path: " + ifile.getFullPath().toString());
        // IResource resource = ifile;
        // try
        // {
        System.out.println("Starting marker code;");
        // IMarker marker = resource.createMarker("org.lamport.tla.toolbox.editor.basic.showUse");
        // Map markerAttributes = new HashMap(2);
        // markerAttributes.put(IMarker.CHAR_START, new Integer(0));
        // markerAttributes.put(IMarker.CHAR_END, new Integer(50));
        // marker.setAttributes(markerAttributes);
        // System.out.println("Ending marker code;");
        //            
        //
        // } catch (CoreException e)
        // {
        // // TODO Auto-generated catch block
        // System.out.println("Exception thrown by marker code;");
        // }
        //
        //
        // Compute locations of the uses. Must look at the OpApplNode's syntax node tree
        // and check for the following cases:
        // Foo(...) : the node is an N_OpApplication node, it's
        // first child is an N_GeneralID whose location is good.
        // ... %% ... : the node is an N_InfixExpr node, whose 2nd child is
        // an N_GenInfixOp whose location is good.
        // x : the node is an N_GeneralID node whose location is good
        // ...^+ : the node is an N_PostfixExpr node whose second heir
        // is an N_GeneralPostfixOp whose location is good
        return null;
    }

    /**
     * A comparator to compare two locations.  It must only be used
     * to compare Location objects.
     * @author lamport
     *
     */
    private class LocationComparator implements Comparator
    {
        public int compare(Object arg0, Object arg1)
        {
            // Most of this code is a clone from SemanticNode.compareTo
            Location loc1 = (Location) arg0;
            Location loc2 = (Location) arg1;
            if (loc1.beginLine() < loc2.beginLine())
            {
                return -1;
            }
            if (loc1.beginLine() > loc2.beginLine())
            {
                return 1;
            }
            if (loc1.beginColumn() == loc2.beginColumn())
            {
                return 0;
            }
            return (loc1.beginColumn() < loc2.beginColumn()) ? -1 : 1;
        }

    }
}
