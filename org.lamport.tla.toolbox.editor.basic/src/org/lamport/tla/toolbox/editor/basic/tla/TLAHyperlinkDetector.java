package org.lamport.tla.toolbox.editor.basic.tla;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.hyperlink.AbstractHyperlinkDetector;
import org.eclipse.jface.text.hyperlink.IHyperlink;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.actions.OpenDeclarationAction;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil.StringAndLocation;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.Context;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tla2sany.st.Location;
import util.UniqueString;

/**
 * Detects hyperlinks in TLA+ code
 * 
 * The hyperlinks in a module editor are the identifiers whose 
 * definitions or declarations are in the root module--meaning they are
 * in the root module, in EXTENDed modules, or are imported with an INSTANCE
 * statement.  The detectHyperlinks method returns an array of at most one
 * object, which is an OpenDeclarationAction object.  See the comments
 * in TLAEditor.java for the OpenDeclarationHandler nested class.
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAHyperlinkDetector extends AbstractHyperlinkDetector
{

    public TLAHyperlinkDetector()
    {
    }

    /**
     * This method first sets label to the token at the position indicated by the
     * region.  If the module is parsed and unmodified, it uses EditorUtil.getTokenAt
     * to do that from the syntax tree.  Otherwise, it uses DocumentHelper.getRegionExpandedBoth
     * to try to do it from the actual text in the buffer.  This method, written by Simon,
     * works only if the region actually indicates the entire token, if it is inside
     * an Identifier, or in certain other cases if it is lucky.
     * 
     * It then currently tries to look up label in the module's symbol table.  It thus finds
     * only globally defined symbols.  It should be modified so that, if that fails and 
     * the module is parsed and unmodified, then it goes down the semantic tree trying to 
     * find a local definition for the label. 
     * 
     * It also needs to be modified to look up the symbol in the module whose editor
     * has the focus, instead of in the root module--at least, if the spec
     * is parsed and that module in the spec.
     * 
     * This was modified by LL on 12 June 2010 so that, for identifiers like Foo!bar!X, 
     * it produces a hyperlink to the definition of X in the source module.
     */
    public IHyperlink[] detectHyperlinks(ITextViewer textViewer, IRegion region, boolean canShowMultipleHyperlinks)
    {
        if (ToolboxHandle.getSpecObj() == null)
        {
            // no spec
            return null;
        }

        IDocument document = textViewer.getDocument();

        // Set goodLabel to the real label, obtained from the syntax tree.
        StringAndLocation goodLabelAndLoc = EditorUtil.getTokenAt(document, region.getOffset(), region.getLength());

        // Set label to the label to be used, which is goodLabel if that is not null,
        // else is the label computed by Simon's approximate method that just looks at
        // the actual text in the editor.
        String label = null;
        Location location = null; // LL.
        if (goodLabelAndLoc != null)
        {
            label = goodLabelAndLoc.string;
            location = goodLabelAndLoc.location;
            try
            {
                region = DocumentHelper.locationToRegion(document, goodLabelAndLoc.location);
            } catch (BadLocationException e)
            {
                System.out.println("Bad location");
                // If there's an exception, we just won't get
                // a visible hyperlink.
            }
        } else
        {
            location = EditorUtil.getLocationAt(document, region.getOffset(), region.getLength());
        }

        try
        {
            if (label == null)
            {

                if (region.getLength() == 0)
                {
                    region = DocumentHelper.getRegionExpandedBoth(document, region.getOffset(), DocumentHelper
                            .getDefaultWordDetector());
                }
                label = document.get(region.getOffset(), region.getLength());
            }
            // System.out.println("Hyperlink request at position " + region.getOffset() + " for '" + label + "'");

            // Context context = ToolboxHandle.getSpecObj().getExternalModuleTable().getRootModule().getContext();
            // SymbolNode resolvedSymbol = context.getSymbol(UniqueString.uniqueStringOf(label));

            // Find the module editor and, if it exists, set moduleNode to 
            // the ModuleNode of the module it is editing.  If that's not null,
            // look up the label at its location in that module.
            TLAEditor editor = EditorUtil.getTLAEditorWithFocus();
            if (editor == null) {
                return null;
            }
            String moduleName = editor.getModuleName();
            ModuleNode moduleNode = ResourceHelper.getModuleNode(moduleName);
            if (moduleNode == null) {
                return null;
            }
            SymbolNode resolvedSymbol = EditorUtil.lookupSymbol(UniqueString.uniqueStringOf(label), moduleNode,
                    location, null);

            // try symbols (does not work for module nodes)
            if (resolvedSymbol != null)
            {
                // If this symbol was imported by instantiation from
                // another module, we set resolvedSymbol to its
                // definition in that module.
                if (resolvedSymbol instanceof OpDefNode)
                {
                    OpDefNode opdef = (OpDefNode) resolvedSymbol;
                    if (opdef.getSource() != null)
                    {
                        resolvedSymbol = opdef.getSource();
                    }
                }
                SyntaxTreeNode csNode = (SyntaxTreeNode) resolvedSymbol.getTreeNode();
                for (int i = 0; i < csNode.getAttachedComments().length; i++)
                {
                    System.out.println(csNode.getAttachedComments()[i]);
                }

                IResource resource = null;
                // 
                if (ToolboxHandle.isUserModule(ResourceHelper.getModuleFileName(csNode.getFilename())))
                {
                    // resource
                    resource = ResourceHelper.getResourceByModuleName(csNode.getFilename());
                } else
                {
                    // System.out.println("A StandardModule '" + csNode.getFilename() + "' is requested...");
                    return null;
                }

                // connect to the resource
                FileEditorInput fileEditorInput = new FileEditorInput((IFile) resource);
                FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
                try
                {
                    fileDocumentProvider.connect(fileEditorInput);
                    document = fileDocumentProvider.getDocument(fileEditorInput);
                } finally
                {
                    /*
                     * Once the document has been retrieved, the document provider is
                     * not needed. Always disconnect it to avoid a memory leak.
                     * 
                     * Keeping it connected only seems to provide synchronization of
                     * the document with file changes. That is not necessary in this context.
                     */
                    fileDocumentProvider.disconnect(fileEditorInput);
                }

                try
                {
                    // Get the location to highlight.  If it's an OpDefNode, just highlight the
                    // left-hand side.
                    if (resolvedSymbol instanceof OpDefNode) {
                        csNode = csNode.getHeirs()[0];
                    } else if (resolvedSymbol instanceof ThmOrAssumpDefNode) {
                        csNode = csNode.getHeirs()[1];
                    }
                    IRegion startLineRegion = document.getLineInformation(csNode.getLocation().beginLine() - 1);
                    IRegion endLineRegion = document.getLineInformation(csNode.getLocation().endLine() - 1);

                    // offsets
                    int startOffset = startLineRegion.getOffset() + csNode.getLocation().beginColumn() - 1;
                    int endOffset = endLineRegion.getOffset() + csNode.getLocation().endColumn();

                    return new IHyperlink[] { new OpenDeclarationAction(resource, new Region(startOffset, endOffset
                            - startOffset), label, region) };

                } catch (BadLocationException e)
                {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
        } catch (BadLocationException e)
        {
            e.printStackTrace();
            // error reading the target
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }
}
