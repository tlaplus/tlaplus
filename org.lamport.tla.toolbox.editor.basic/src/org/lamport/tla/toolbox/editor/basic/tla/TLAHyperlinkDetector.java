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
import org.lamport.tla.toolbox.ui.handler.OpenModuleHandler;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParserConstants;
import tla2sany.semantic.Context;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tla2sany.st.Location;
import tla2sany.st.SyntaxTreeConstants;
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
     * 
     * It was completely modified again by LL in Sep 2010 to use TokenSpec.findTokenSpecs,
     * so it handles approximately all symbol occurrences using only the text and the last 
     * module parse.
     * 
     * Note: This method is called by the Eclipse infrastructure to show hyperlinks 
     * when the user holds down the Control key and moves the mouse.  It is called
     * by TLAEditor$OpenDeclarationHandler.execute to implement the Open Declaration
     * command.
     */
    public IHyperlink[] detectHyperlinks(ITextViewer textViewer, IRegion region, boolean canShowMultipleHyperlinks)
    {
        if (ToolboxHandle.getSpecObj() == null)
        {
            // no spec
            return null;
        }

        IDocument document = textViewer.getDocument();

        // set currentTokenSpec to the TokenSpec object specifying the
        // currently selected symbol and its resolution.
        TokenSpec currentTokenSpec = TokenSpec.findCurrentTokenSpec(region);
        if (currentTokenSpec == null)
        {
            return null;
        }

        // Set region to the Region of the document described by currentTokenSpec
        // (this ugly re-use of a parameter name is kept from Simon's original
        // code), set label to the found symbol name, and set resolvedSymbol to
        // the SymbolNode.
        region = new Region(currentTokenSpec.leftPos, currentTokenSpec.rightPos - currentTokenSpec.leftPos);
        String label = currentTokenSpec.token;
        SymbolNode resolvedSymbol = currentTokenSpec.resolvedSymbol;
        try
        {
            // If it didn't find the symbol, check if this is a module name and, if
            // so, set resolvedSymbol to the module node.
            if (resolvedSymbol == null /* && label != null */)
            {
                resolvedSymbol = ResourceHelper.getModuleNode(label);
            }

            // try symbols (does not work for module nodes)
            if (resolvedSymbol != null)
            {
                // If this symbol was imported by instantiation from
                // another module, we set resolvedSymbol to its
                // definition in that module.
                // LL Sep 2010: The comment above doesn't make sense since we're
                // not setting resolvedSymbol. I suppose the code was changed
                // at some point without changing the comment.
                SyntaxTreeNode csNode = (SyntaxTreeNode) resolvedSymbol.getTreeNode();

                // If this is a module, we want csNode to be the SyntaxTreeNode of just the name.
                // However, for some reason, that node doesn't have a file name. So we set
                // csNode to be the node representing the whole "---- MODULE foo -----",
                // which works and is perhaps even better.
                if (resolvedSymbol instanceof ModuleNode)
                {
                    csNode = (SyntaxTreeNode) resolvedSymbol.stn.heirs()[0]; // .heirs()[1];
                }
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
                    // Get the location to highlight. If it's an OpDefNode, want
                    // to get just the symbol from the left-hand side. (Otherwise,
                    // the user can't execute Goto Declaration immediately followed
                    // by Show Uses.)
                    if (resolvedSymbol instanceof OpDefNode)
                    {
                        // Need to pick out the symbol from the left-hand side of
                        // the definition.
                        csNode = csNode.getHeirs()[0];
                        if (csNode.getKind() == SyntaxTreeConstants.N_IdentLHS)
                        {
                            csNode = csNode.getHeirs()[0];
                        } else
                        {
                            if ((csNode.getKind() == SyntaxTreeConstants.N_InfixLHS)
                                    || (csNode.getKind() == SyntaxTreeConstants.N_PostfixLHS))
                            {
                                csNode = csNode.getHeirs()[1];
                            }
                        }
                    } else if ((resolvedSymbol instanceof ThmOrAssumpDefNode)
                            && ((csNode.getKind() == SyntaxTreeConstants.N_Theorem) || (csNode.getKind() == SyntaxTreeConstants.N_Assumption)))
                    {
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
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }
}
