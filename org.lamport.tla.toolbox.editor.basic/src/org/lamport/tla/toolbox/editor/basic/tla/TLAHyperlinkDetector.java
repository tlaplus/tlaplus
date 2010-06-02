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
import org.lamport.tla.toolbox.editor.basic.actions.OpenDeclarationAction;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.SymbolNode;
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

    public IHyperlink[] detectHyperlinks(ITextViewer textViewer, IRegion region, boolean canShowMultipleHyperlinks)
    {
        if (ToolboxHandle.getSpecObj() == null)
        {
            // no spec
            return null;
        }

        String label = null;

        IDocument document = textViewer.getDocument();
        try
        {
            if (region.getLength() == 0)
            {
                region = DocumentHelper.getRegionExpandedBoth(document, region.getOffset(), DocumentHelper
                        .getDefaultWordDetector());
            }
            label = document.get(region.getOffset(), region.getLength());

            // System.out.println("Hyperlink request at position " + region.getOffset() + " for '" + label + "'");

            SymbolNode resolvedSymbol = ToolboxHandle.getSpecObj().getExternalModuleTable().getRootModule()
                    .getContext().getSymbol(UniqueString.uniqueStringOf(label));

            // try symbols (does not work for module nodes)
            if (resolvedSymbol != null)
            {
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
                    // find the line in the document
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
