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
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.semantic.SymbolNode;
import tla2sany.st.TreeNode;
import util.UniqueString;

/**
 * Detects hyperlinks in TLA+ code
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
        if (region.getLength() == 0)
        {
            System.out.println("Hyperlink request at position " + region.getOffset());
            // TODO
        }
        if (ToolboxHandle.getSpecObj() == null)
        {
            // no spec
            return null;
        }

        String label = null;

        IDocument document = textViewer.getDocument();
        try
        {
            label = document.get(region.getOffset(), region.getLength());

            SymbolNode resolvedSymbol = ToolboxHandle.getSpecObj().getExternalModuleTable().getRootModule()
                    .getContext().getSymbol(UniqueString.uniqueStringOf(label));

            // try symbols (does not work for module nodes)
            if (resolvedSymbol != null)
            {
                TreeNode csNode = resolvedSymbol.getTreeNode();

                IResource resource = null;
                // 
                if (ToolboxHandle.isUserModule(ResourceHelper.getModuleFileName(csNode.getFilename())))
                {
                    // resource
                    resource = ResourceHelper.getResourceByModuleName(csNode.getFilename());
                } else
                {
                    System.out.println("A StandardModule '" + csNode.getFilename() + "' is requested...");
                    return null;
                }

                // connect to the resource
                FileEditorInput fileEditorInput = new FileEditorInput((IFile) resource);
                FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
                fileDocumentProvider.connect(fileEditorInput);
                document = fileDocumentProvider.getDocument(fileEditorInput);
                
                try
                {
                    // find the line in the document
                    IRegion startLineRegion = document.getLineInformation(csNode.getLocation().beginLine() - 1);
                    IRegion endLineRegion = document.getLineInformation(csNode.getLocation().endLine() - 1);

                    // offsets
                    int startOffset = startLineRegion.getOffset() + csNode.getLocation().beginColumn() - 1;
                    int endOffset = endLineRegion.getOffset() + csNode.getLocation().endColumn();

                    return new IHyperlink[] { new OpenDeclarationAction(resource, new Region(startOffset, endOffset
                            - startOffset), label) };

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
