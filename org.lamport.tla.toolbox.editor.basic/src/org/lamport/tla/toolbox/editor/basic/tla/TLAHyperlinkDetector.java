package org.lamport.tla.toolbox.editor.basic.tla;

import java.io.File;

import org.eclipse.core.filesystem.EFS;
import org.eclipse.core.filesystem.IFileStore;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Path;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.hyperlink.AbstractHyperlinkDetector;
import org.eclipse.jface.text.hyperlink.IHyperlink;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.editors.text.TextFileDocumentProvider;
import org.eclipse.ui.ide.FileStoreEditorInput;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.editor.basic.TLAEditorReadOnly;
import org.lamport.tla.toolbox.editor.basic.actions.OpenDeclarationAction;
import org.lamport.tla.toolbox.editor.basic.actions.OpenDeclarationInCurrentAction;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tla2sany.st.SyntaxTreeConstants;
import util.FilenameToStream;

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
                
                // Before using the default TLA+ editor below, try to identify and reuse the current
                // editor if it shows the same module already.
                final TLAEditor tlaEditor = EditorUtil.getTLAEditorWithFocus();
				if (tlaEditor != null && csNode.getLocation().source().equals(tlaEditor.getModuleName())) {
					final IDocument document = tlaEditor.getDocumentProvider().getDocument(tlaEditor.getEditorInput());
					final int[] region2 = getRegion(getCS(resolvedSymbol, csNode), document);
					return new IHyperlink[] { new OpenDeclarationInCurrentAction(tlaEditor,
							new Region(region2[0], region2[1] - region2[0]), label, region) };
				}
                
				IDocumentProvider documentProvider = null;
				IEditorInput editorInput = null;
				String editorId = "";
				//
				final FilenameToStream resolver = ToolboxHandle.getSpecObj().getResolver();
				if (ToolboxHandle.isUserModule(ResourceHelper.getModuleFileName(csNode.getFilename()))) {
					editorId = TLAEditorAndPDFViewer.ID;
					editorInput = new FileEditorInput(
							(IFile) ResourceHelper.getResourceByModuleName(csNode.getFilename()));
					documentProvider = new FileDocumentProvider();
				} else if (resolver.isStandardModule(csNode.getFilename())) {
					// No point editing standard modules.
					editorId = TLAEditorReadOnly.ID;

					// Resolve the file via the FilenameToStream resolver in case a user has
					// provided its own standard module definition.
					final File resolved = resolver.resolve(csNode.getFilename(), true);

					// Standard modules live outside the workspace which is why they have to be
					// opened with EFS and read with a TextFileDocumentProvider.
					final IFileStore fileStore = EFS.getLocalFileSystem()
							.getStore(new Path(resolved.getAbsolutePath()));
					editorInput = new FileStoreEditorInput(fileStore);
					documentProvider = new TextFileDocumentProvider();
				} else {
					// A TLA+ built-in module.
					return null;
				}

                final int[] region2 = getDocumentAndRegion(getCS(resolvedSymbol, csNode), documentProvider, editorInput);
				return new IHyperlink[] { new OpenDeclarationAction(editorId, editorInput,
						new Region(region2[0], region2[1] - region2[0]), label, region) };
	           }
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }

	private int[] getDocumentAndRegion(SyntaxTreeNode csNode, IDocumentProvider documentProvider, IEditorInput editorInput)
			throws CoreException {
		IDocument document;
		// connect to the resource
		try {
			documentProvider.connect(editorInput);
			document = documentProvider.getDocument(editorInput);
		} finally {
			/*
			 * Once the document has been retrieved, the document provider is not needed.
			 * Always disconnect it to avoid a memory leak.
			 * 
			 * Keeping it connected only seems to provide synchronization of the document
			 * with file changes. That is not necessary in this context.
			 */
			documentProvider.disconnect(editorInput);
		}

		return getRegion(csNode, document);
	}

	private int[] getRegion(SyntaxTreeNode csNode, IDocument document) {
		try {
			IRegion startLineRegion = document.getLineInformation(csNode.getLocation().beginLine() - 1);
			IRegion endLineRegion = document.getLineInformation(csNode.getLocation().endLine() - 1);

			// offsets
			int startOffset = startLineRegion.getOffset() + csNode.getLocation().beginColumn() - 1;
			int endOffset = endLineRegion.getOffset() + csNode.getLocation().endColumn();

			return new int[] { startOffset, endOffset };
		} catch (BadLocationException e) {
			e.printStackTrace();
		}
		return new int[] { 0, 0 };
	}

	private SyntaxTreeNode getCS(SymbolNode resolvedSymbol, SyntaxTreeNode csNode) {
		// Get the location to highlight. If it's an OpDefNode, want
		// to get just the symbol from the left-hand side. (Otherwise,
		// the user can't execute Goto Declaration immediately followed
		// by Show Uses.)
		if (resolvedSymbol instanceof OpDefNode && csNode.getHeirs().length >= 1) {
			// Need to pick out the symbol from the left-hand side of
			// the definition.
			csNode = csNode.getHeirs()[0];
			if (csNode.getKind() == SyntaxTreeConstants.N_IdentLHS) {
				csNode = csNode.getHeirs()[0];
			} else {
				if ((csNode.getKind() == SyntaxTreeConstants.N_InfixLHS)
						|| (csNode.getKind() == SyntaxTreeConstants.N_PostfixLHS)) {
					csNode = csNode.getHeirs()[1];
				}
			}
		} else if ((resolvedSymbol instanceof ThmOrAssumpDefNode && csNode.getHeirs().length >= 2)
				&& ((csNode.getKind() == SyntaxTreeConstants.N_Theorem)
						|| (csNode.getKind() == SyntaxTreeConstants.N_Assumption))) {
			csNode = csNode.getHeirs()[1];
		}
		return csNode;
	}
}
