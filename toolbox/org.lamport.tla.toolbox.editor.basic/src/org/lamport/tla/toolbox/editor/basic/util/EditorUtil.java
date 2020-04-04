package org.lamport.tla.toolbox.editor.basic.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ResourceMarkerAnnotationModel;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper.WordRegion;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import pcal.TLAtoPCalMapping;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.Operators;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.AssumeProveNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NewSymbNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tla2sany.st.Location;
import tla2sany.st.SyntaxTreeConstants;
import util.UniqueString;

/**
 * A collection of useful editor methods.
 * 
 * @author ricketts
 *
 */
public class EditorUtil
{

    /**
     * Type of the marker that contains a boolean attribute indicating if the module on which
     * the marker is placed should be read-only.
     */
    public static final String READ_ONLY_MODULE_MARKER = "org.lamport.tla.toolbox.editor.basic.readOnly";
    /**
     * ID for the boolean attribute for {@link EditorUtil#READ_ONLY_MODULE_MARKER} indicating if
     * the module should be read only.
     */
    public static final String IS_READ_ONLY_ATR = "org.lamport.tla.toolbox.editor.basic.isReadOnly";

    /**
     * Returns the {@link TLAEditor} with focus or null if
     * there is none.
     * 
     * This must be run in a a UI thread. See {@link UIHelper#runUIAsync(Runnable)}
     * and {@link UIHelper#runUISync(Runnable)}.
     * 
     * @return
     */
    public static TLAEditor getTLAEditorWithFocus()
    {
		IEditorPart activeEditor = UIHelper.getActiveEditor();
		if (activeEditor instanceof TLAEditorAndPDFViewer) {
			TLAEditor editor = ((TLAEditorAndPDFViewer) activeEditor).getTLAEditor();
			if (editor != null && editor.getViewer().getTextWidget().isFocusControl()) {
				return editor;
			}
		} else if (activeEditor != null && activeEditor.getAdapter(TLAEditor.class) != null) {
			TLAEditor editor = activeEditor.getAdapter(TLAEditor.class);
			if (editor != null && editor.getViewer().getTextWidget().isFocusControl()) {
				return editor;
			}
		}
        return null;
    }

    /**
     * Returns the currently active {@link TLAEditor}
     * in the toolbox. This {@link TLAEditor} may not have focus
     * or may not even be visible. If there is an editor showing
     * in the toolbox and the editor is a {@link TLAEditorAndPDFViewer},
     * then the {@link TLAEditor} from that multipage editor
     * will be returned. Else, this method returns null.
     * 
     * @return
     */
    public static TLAEditor getActiveTLAEditor()
    {
        IEditorPart activeEditor = UIHelper.getActiveEditor();
        // activeEditor.getAdapter(ITexto)
        if (activeEditor instanceof TLAEditorAndPDFViewer)
        {
            return ((TLAEditorAndPDFViewer) activeEditor).getTLAEditor();
		}

        return activeEditor.getAdapter(TLAEditor.class);
    }

    /**
     * returns true iff the location loc1 is contained within location loc2,
     * where the file names of the locations are ignored.
     * 
     * @param loc1
     * @param loc2
     * @return
     */
    public static boolean locationContainment(Location loc1, Location loc2)
    {
        if ((loc1.beginLine() < loc2.beginLine())
                || ((loc1.beginLine() == loc2.beginLine()) && (loc1.beginColumn() < loc2.beginColumn())))
        {
            return false;
        }
        return (loc1.endLine() < loc2.endLine())
                || ((loc1.endLine() == loc2.endLine()) && (loc1.endColumn() <= loc2.endColumn()));
    }
    
    /**
     * True iff the range of lines specified by loc1 is a subset of the range of lines
     * specified by loc2.
     * 
     * @param loc1
     * @param loc2
     * @return
     */
    public static boolean lineLocationContainment(Location loc1, Location loc2) {
    	return (loc1.beginLine() >= loc2.beginLine()) && (loc2.endLine() >= loc1.endLine()) ;
    }

    /**
     * Returns the TLA+ token in the document containing the region delimited
     * by the offset and length.  A token here means a TLA+ token except
     * that a name like Foo!bar!x is considered to be a single token.  It
     * returns null if the file is not parsed or the editor is dirty (so there
     * is no useful information in the parse tree) or if there is no token
     * contained within the indicated region.
     * 
     * Note: The reason the arguments are an offset and a length is because
     * Eclipse sometimes gives a region of a document as an IRegion and
     * sometimes as an ISelection.  And even though an ISelection implements
     * all the methods of an IRegion, the builders of Eclipse in their infinite
     * wisdom chose not to declare an ISelection to implement an IRegion,
     * and I didn't feel like creating an interface that implements both
     * of them.

     * 
     * @param document
     * @param offset
     * @param length
     * @return
     */
    public static StringAndLocation getTokenAt(IDocument document, int offset, int length)
    {
        Location location = getLocationAt(document, offset, length);
        return getTokenAtLocation(location);
    }

    /**
     * Returns the token containing the current selection, or null
     * if there is none.  A token here means a TLA+ token except
     * that a name like Foo!bar!x is considered to be a single token.  It
     * returns null if the file is not parsed or the editor is dirty (so there
     * is no useful information in the parse tree) or if there is no token
     * contained within the indicated region.
     * 
     * THIS METHOD DOES NOT SEEM TO BE USED.
     * @return
     */
    public static StringAndLocation getCurrentToken()
    {
        Location location = getCurrentLocation();
        if (location == null)
        {
            return null;
        }

        return getTokenAtLocation(location);
    }

    /**
     * On 21 June 2010 LL discovered the following bug.  For a proof-step number of the form "<2>3.", the token in the
     * syntax tree contains the ".".  This seems to be a reasonable place to fix it by returning just the "<2>3" and
     * its location.  Apparently, it has been fixed here.
     *  
     * @param location
     * @return
     */
    public static StringAndLocation getTokenAtLocation(Location location)
    {
        TLAEditor editor = EditorUtil.getTLAEditorWithFocus();
        // This method is called only when there is a TLAEditor with
        // the focus, so I don't see how it could be null. However,
        // while debugging, that did happen in some unreproducible
        // fashion.
        if (editor == null)
        {
            return null;
        }
        IFile moduleFile = ((FileEditorInput) editor.getEditorInput()).getFile();

        if (editor.isDirty())
        {
        	TLAEditorActivator.getDefault().logDebug("Editor is dirty");
            return null;
        }

        // Return null if the file is not parsed.
        ParseResult parseResult = ResourceHelper.getValidParseResult(moduleFile);
        if ((parseResult == null) || (parseResult.getStatus() != IParseConstants.PARSED))
        {
            return null;
        }

        // get module node (code copied from
        // ResourceHelper.getPfStepOrUseHideFromMod)
        String moduleName = ResourceHelper.getModuleName(moduleFile);
        ModuleNode module = parseResult.getSpecObj().getExternalModuleTable().getModuleNode(
                UniqueString.uniqueStringOf(moduleName));
        if (module == null)
        {
            return null;
        }
        SyntaxTreeNode stn = (SyntaxTreeNode) module.stn;
        if (!locationContainment(location, stn.getLocation()))
        {
            return null;
        }

        StringAndLocation stl = innerGetCurrentToken(stn, location);
        if (stl == null)
        {
            return null;
        }
        if ((stl.string.charAt(0) == '<') && (stl.string.indexOf('.') != -1))
        {
            Location loc = stl.location;
            stl = new StringAndLocation(stl.string.substring(0, stl.string.indexOf('.')), new Location(UniqueString
                    .uniqueStringOf(loc.source()), loc.beginLine(), loc.beginColumn(), loc.endLine(), loc.beginColumn()
                    + stl.string.indexOf('.')));
        }
        return stl;
    }

    /**
     * The inner method of getCurrentToken.  It assumes that
     * location is contained within stn.location.
     * 
     * @param stn
     * @param location
     * @return
     */
    private static StringAndLocation innerGetCurrentToken(SyntaxTreeNode stn, Location location)
    {
        int kind = stn.getKind();
        if (kind == SyntaxTreeConstants.N_GeneralId
        // || kind == SyntaxTreeConstants.N_GenNonExpPrefixOp
        // || kind == SyntaxTreeConstants.N_GenPrefixOp || kind == SyntaxTreeConstants.N_GenPostfixOp
        )
        {
            // TLAEditorActivator.getDefault().logDebug("Returning concatenation of heirs: " + concatHeirTokens(stn));
            return new StringAndLocation(concatHeirTokens(stn), stn.getLocation());
        }
        // TLAEditorActivator.getDefault().logDebug("Called on node kind = " + stn.getKind() +
        // ", image = `" + stn.getImage() + "'");
        SyntaxTreeNode[] heirs = stn.getHeirs();
        if (heirs.length == 0)
        {
            // TLAEditorActivator.getDefault().logDebug("Hit bottom, returning " + stn.getImage());
            return new StringAndLocation(stn.getImage(), stn.getLocation());
        }
        for (int i = 0; i < heirs.length; i++)
        {
            if (locationContainment(location, heirs[i].getLocation()))
            {
                // TLAEditorActivator.getDefault().logDebug("Recursing");
                return innerGetCurrentToken(heirs[i], location);
            }
        }
        // TLAEditorActivator.getDefault().logDebug("Not found; return null");
        return null;
    }

    /**
     * Returns the concatenation of the images of all leaf nodes
     * of the node stn that correspond to actual tokens
     * 
     * @param stn
     * @return
     */
    private static String concatHeirTokens(SyntaxTreeNode stn)
    {
        SyntaxTreeNode[] heirs = stn.getHeirs();
        if (heirs.length == 0)
        {
            // A a node of kind >= NULL_ID with no heirs should
            // (I think) only be an empty N_IdPrefix.
            if (stn.getKind() < SyntaxTreeConstants.NULL_ID)
            {
                return stn.getImage();
            } else
            {
                return "";
            }
        }
        String val = "";
        for (int i = 0; i < heirs.length; i++)
        {
            val = val + concatHeirTokens(heirs[i]);
        }
        return val;
    }

    /**
     * Returns a Location corresponding to the current selection of the
     * {@link TLAEditor} that has the focus, except with a null file 
     * (module) name.  (To find the code for getting the name, see  
     * ProverHelper.runProverForActiveSelection.
     * 
     * Returns null if anything goes wrong when trying to compute the
     * location.
     * 
     * @return
     */
    public static Location getCurrentLocation()
    {
		return getCurrentLocation(0);
    }
    
    /**
     * Like getCurrentLocation, except it adds x to the result's endCol
     * field.  For some reason, computing the region of the PlusCal code 
     * corresponding to a region in the TLA+ translation calls this
     * method with x=1.
     * 
     * @param x
     * @return
     */
    public static Location getCurrentLocation(int x)
    {
        ITextSelection selection = getCurrentSelection();
		return getLocationAt(getCurrentDocument(), selection.getOffset(), selection.getLength(), x);
    }
    
    private static IDocument getCurrentDocument() {
        TLAEditor editor = getTLAEditorWithFocus();
        // editor shouldn't be null, but just in case...
        if (editor == null)
        {
            return null;
        }
        return editor.getDocumentProvider().getDocument(editor.getEditorInput());
    }
    
    private static ITextSelection getCurrentSelection() {
        TLAEditor editor = getTLAEditorWithFocus();
        return (ITextSelection) editor.getSelectionProvider().getSelection();
    }

    /**
     * This returns the region in <code>document</code> represented by the
     * <code>location</code>.  Note that a <code>Location</code> is a region
     * represented by the <row, column> coordinates of its first and last 
     * characters.
     * @param document
     * @param location
     * @return
     * @throws BadLocationException
     */
    public static IRegion getRegionOf(IDocument document, Location location)
               throws BadLocationException {
        int offset;
        int length;
        offset = document.getLineInformation(location.beginLine()-1).getOffset()
                            + location.beginColumn() -1;
        length = document.getLineInformation(location.endLine()-1).getOffset()
                          + location.endColumn() - offset;
        return new Region(offset, length) ;
    }
    
    public static Location getLocationAt(IDocument document, int offset, int length)
    {
    	return getLocationAt(document, offset, length, 0);
    }
    
    /**
     * Like getLocationAt, except it adds x to the endCol.
     * 
     * @param document
     * @param offset
     * @param length
     * @param x
     * @return
     */
    public static Location getLocationAt(IDocument document, int offset, int length, int x)
    {
        // I don't think document or selection can be null, but...
        if (document == null)
        {
            return null;
        }
        Location loc = null;
        try
        {
            // Compute the lines in Java coordinates and the columns
            // in human coordinates.
            int startOffset = offset;
            int startLine = document.getLineOfOffset(startOffset);
            int startCol = startOffset - document.getLineOffset(startLine) + 1;
            int endOffset = startOffset + length;
            int endLine = document.getLineOfOffset(endOffset);
            int endCol = endOffset - document.getLineOffset(endLine);
            // Because endCol points to the character to the right of
            // the selection, it now is in human coordinates for the
            // last character of the selection--except if the selection
            // has length 0.
            if (length == 0)
            {
                endCol++;
            }
            loc = new Location(startLine + 1, startCol, endLine + 1, endCol + x);
        } catch (BadLocationException e)
        {
            return null;
            // e.printStackTrace();
        }
        return loc;
    }
    
    /**
     * @see EditorUtil#lookupSymbol(UniqueString, SemanticNode, Location, SymbolNode)
     */
 	public static SymbolNode lookupSymbol(SpecObj specObj, IDocument document, WordRegion region) {
		final Location location = getLocationAt(document, region.getOffset(), region.getLength());
		final ModuleNode rootModule = specObj.getExternalModuleTable().getRootModule();
		return lookupSymbol(UniqueString.uniqueStringOf(region.getWord()), rootModule, location, null);
	}
    
 	/**
 	 * @see EditorUtil#lookupSymbol(UniqueString, SemanticNode, Location, SymbolNode)
 	 */
	public static SymbolNode lookupSymbol(String name, SymbolNode curNode, IDocument document, IRegion region,
			SymbolNode defaultResult) {
		final Location location = getLocationAt(document, region.getOffset(), region.getLength());
		return lookupSymbol(UniqueString.uniqueStringOf(name), curNode, location, defaultResult);
	}

    /**
     * This method is called externally with <code>curNode</code> equal to
     * a ModuleNode and <code>defaultResult</code> equal to <code>null</code>.
     * It then returns the SymbolNode that defines or declares the symbol
     * named <code>name</code> located at <code>location</code>.  For example,
     * in
     * <pre>
     *    foo == \A s \in {s \in T : Find(s)} : AnotherInstance(s)
     *    s == SomeDefinition
     * </pre>
     * if <code>name</code> is the UniqueString of "s" and <code>location</code>
     * is the position of the s in Find(s), then it returns the SymbolNode for
     * the s declared in the set constructor. <p>
     * <p>
     * If no declaration is found, it returns <code>null</code>.<p>
     * <p>
     * It is implemented by using the getChildren() method to walk down the semantic
     * tree towards the symbol's location.  In the recursive call, <code>curNode</code>
     * is the node within which we are looking, and <code>defaultResult</code> is the
     * lowest-level SymbolNode defining <code>name</code> that has been found.
     * 
     * @param name
     * @param curNode
     * @param location
     * @param defaultResult
     */
    public static SymbolNode lookupSymbol(UniqueString name, SemanticNode curNode, Location location,
            SymbolNode defaultResult)
    {
        SymbolNode foundSymbol = null;
        if (curNode instanceof ModuleNode)
        {
            foundSymbol = ((ModuleNode) curNode).getContext().getSymbol(name);
        } else if (curNode instanceof LetInNode)
        {
            foundSymbol = ((LetInNode) curNode).context.getSymbol(name);
        } else if (curNode instanceof NonLeafProofNode)
        {
            foundSymbol = ((NonLeafProofNode) curNode).getContext().getSymbol(name);
        } else if (curNode instanceof OpApplNode)
        {
            OpApplNode oan = (OpApplNode) curNode;
            FormalParamNode[] fpn = oan.getUnbdedQuantSymbols();
            if (fpn != null)
            {
                for (int i = 0; i < fpn.length; i++)
                {
                    if (fpn[i].getName() == name)
                    {
                        // return fpn[i];
                        foundSymbol = fpn[i];
                        break;
                    }
                }
            }

            FormalParamNode[][] fpnA = oan.getBdedQuantSymbolLists();
            if (fpnA != null)
            {
                for (int i = 0; i < fpnA.length; i++)
                {
                    for (int j = 0; j < fpnA[i].length; j++)
                    {
                        if (fpnA[i][j].getName() == name)
                        {
                            // return fpnA[i][j];
                            foundSymbol = fpnA[i][j];
                            i = fpnA.length;
                            break;
                        }
                    }
                }
            }
        } else if (curNode instanceof OpDefNode)
        {
            FormalParamNode[] params = ((OpDefNode) curNode).getParams();
            for (int i = 0; i < params.length; i++)
            {
                if (name == params[i].getName())
                {
                    // return params[i];
                    foundSymbol = params[i];
                    break;
                }
            }
        } else if (curNode instanceof TheoremNode)
        {
            TheoremNode thm = (TheoremNode) curNode;
            LevelNode assertion = thm.getTheorem();

            if (assertion instanceof AssumeProveNode)
            {
                AssumeProveNode apn = (AssumeProveNode) assertion;
                SemanticNode[] assumes = apn.getAssumes();
                if (!apn.getSuffices())
                {
                    for (int i = 0; i < assumes.length; i++)
                    {
                        if (assumes[i] instanceof NewSymbNode)
                        {
                            NewSymbNode newSymb = (NewSymbNode) assumes[i];
                            OpDeclNode opDecl = newSymb.getOpDeclNode();
                            if (name == opDecl.getName())
                            {
                                foundSymbol = opDecl;
                                break;
                            }
                        }
                    }
                }
            }
        }
        if (foundSymbol == null)
        {
            foundSymbol = defaultResult;
        }
        SemanticNode[] children = curNode.getChildren();
        if (children == null)
        {
            return foundSymbol;
        }
        for (int i = 0; i < children.length; i++)
        {
            if (locationContainment(location, children[i].getLocation()))
            {
                foundSymbol = lookupSymbol(name, children[i], location, foundSymbol);
            }
        }
        return foundSymbol;
    }

    /**
     *  Like lookupSymbol except that for definitions that were obtained by instantiation
     *  from a definition in another module, it returns the definition from that other module.
     *  
     * @param name
     * @param curNode
     * @param location
     * @param defaultResult
     * @return
     */
    public static SymbolNode lookupOriginalSymbol(UniqueString name, SemanticNode curNode, Location location,
            SymbolNode defaultResult)
    {
        // In case this is a synonym for something else.
        name = Operators.resolveSynonym(name);

        SymbolNode resolvedSymbol = lookupSymbol(name, curNode, location, defaultResult);
        if (resolvedSymbol == null)
        {
            return null;
        }
        if (resolvedSymbol instanceof OpDefNode)
        {
            OpDefNode opdef = (OpDefNode) resolvedSymbol;
            if (opdef.getSource() != null)
            {
                resolvedSymbol = opdef.getSource();
            }
        } else if (resolvedSymbol instanceof ThmOrAssumpDefNode)
        {
            ThmOrAssumpDefNode opdef = (ThmOrAssumpDefNode) resolvedSymbol;
            if (opdef.getSource() != null)
            {
                resolvedSymbol = opdef.getSource();
            }
        }
        return resolvedSymbol;
    }

    /**
     * Returns a TLA editor on moduleFileName and opens it in a window if there isn't 
     * one already open.  It also gives the editor focus.
     * 
     * @param moduleFileName name of the module with .tla extension.
     * @return
     */
    public static TLAEditor openTLAEditor(final String moduleFileName)
    {
        final IResource module = ResourceHelper.getResourceByName(moduleFileName);
		if ((module != null) && (module instanceof IFile)) {
            final IEditorPart editor = UIHelper.openEditor(TLAEditor.ID, (IFile) module);
            
            if (editor instanceof TLAEditor) {
            	return (TLAEditor)editor;
			} else if (editor instanceof TLAEditorAndPDFViewer) {
                return ((TLAEditorAndPDFViewer) editor).getTLAEditor();
            }
        }

        return null;
    }

    /**
     * Tries to find and return a {@link TLAEditor} already open
     * on module. Returns null if one is not found. If there
     * are multiple editors open, this just returns one of them.
     * Which one is unspecified.
     * 
     * @param module
     * @return
     */
    public static TLAEditor findTLAEditor(IResource module)
    {
        if (module != null && module instanceof IFile)
        {
            IEditorPart editor = UIHelper.getActivePage().findEditor(new FileEditorInput((IFile) module));
            if (editor instanceof TLAEditorAndPDFViewer)
            {
                return ((TLAEditorAndPDFViewer) editor).getTLAEditor();
            }
        }

        return null;
    }

    /**
     * If there is currently a TLAEditor with focus, 
     * and that editor is unmodified and is currently parsed,
     * and its cursor is "at" a TheoremNode, then it returns
     * that TheoremNode.  Otherwise, it returns null.
     */
    public static TheoremNode getCurrentTheoremNode()
    {
        // get editor and return null if it doesn't exist or
        // is dirty.
        TLAEditor editor = getTLAEditorWithFocus();
        if ((editor == null) || (editor.isDirty()))
        {
            return null;
        }
        ISelectionProvider selectionProvider = editor.getSelectionProvider();
        Assert.isNotNull(selectionProvider, "Active editor does not have a selection provider. This is a bug.");
        ISelection selection = selectionProvider.getSelection();
        if (!(selection instanceof ITextSelection))
        {
            return null;
        }
        ITextSelection textSelection = (ITextSelection) selection;
        IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());

        // check if editor's file is currently parsed.
        
        if (editor.getEditorInput() instanceof FileEditorInput) {
        	IFile file = ((FileEditorInput) editor.getEditorInput()).getFile();
        	String moduleName = ResourceHelper.getModuleName(file);
        	
        	ParseResult parseResult = ResourceHelper.getValidParseResult(file);
        	
        	return ResourceHelper.getTheoremNodeWithCaret(parseResult, moduleName, textSelection, document);
        }
        return null;
    }

    /**
     *  Returns true iff editor with focus is modified
     */
    public static boolean editorWithFocusDirty()
    {
        return getTLAEditorWithFocus().isDirty();
    }

    /**
     * Returns the name of the module whose editor has focus.
     */
    public static String moduleWithFocus()
    {
        TLAEditor editor = getTLAEditorWithFocus();
        IFile file = ((FileEditorInput) editor.getEditorInput()).getFile();
        String name = ResourceHelper.getModuleName(file);
        return name;
    }

    /**
     * Signals using a marker that the module should be read-only
     * if isReadOnly is true or not read-only if isReadOnly is false.
     * 
     * @param module
     * @param isReadOnly
     * @throws CoreException 
     */
    public static void setReadOnly(IResource module, boolean isReadOnly)
    {
        try
        {

            if (module.exists())
            {
                IMarker marker;
                // Try to find any existing markers.
                IMarker[] foundMarkers = module.findMarkers(READ_ONLY_MODULE_MARKER, false, IResource.DEPTH_ZERO);

                // There should only be one such marker at most.
                // In case there is more than one existing marker,
                // remove extra markers.
                if (foundMarkers.length > 0)
                {
                    marker = foundMarkers[0];
                    // remove trash if any
                    for (int i = 1; i < foundMarkers.length; i++)
                    {
                        foundMarkers[i].delete();
                    }
                } else
                {
                    // Create a new marker if no existing ones.
                    marker = module.createMarker(READ_ONLY_MODULE_MARKER);
                }

                // Set the boolean attribute to indicate if the marker is running.
                marker.setAttribute(IS_READ_ONLY_ATR, isReadOnly);
            }
        } catch (CoreException e)
        {
            Activator.getDefault().logError("Error setting module " + module + " to read only.", e);
        }

    }

    /**
     *  Finds the current editor and calls 
     *  setReturnFromOpenDecl(TLAEditor)
     */
    public static void setReturnFromOpenDecl()
    {
        TLAEditor srcEditor = EditorUtil.getTLAEditorWithFocus();
        setReturnFromOpenDecl(srcEditor);
    }

    /**
     * Sets the location to which the ReturnFromOpenDeclaration command
     * should return to be the current selection of srcEditor.
     * 
     * @param srcEditor
     */
    public static void setReturnFromOpenDecl(TLAEditor srcEditor)
    {
        if (srcEditor != null)
        {
            Spec spec = ToolboxHandle.getCurrentSpec();
            spec.setOpenDeclModuleName(srcEditor);
        }
    }

    /**
     * Returns true iff the module has been set to read only using
     * the method {@link EditorUtil#setReadOnly(IResource, boolean)}.
     * 
     * @param module
     * @return
     * @throws CoreException 
     */
    public static boolean isReadOnly(IResource module)
    {

        try
        {
            if (module.exists())
            {
                IMarker marker;
                // Try to find any existing markers.
                IMarker[] foundMarkers = module.findMarkers(READ_ONLY_MODULE_MARKER, false, IResource.DEPTH_ZERO);

                // There should only be one such marker at most.
                // In case there is more than one existing marker,
                // remove extra markers.
                if (foundMarkers.length > 0)
                {
                    marker = foundMarkers[0];
                    // remove trash if any
                    for (int i = 1; i < foundMarkers.length; i++)
                    {
                        foundMarkers[i].delete();
                    }

                    return marker.getAttribute(IS_READ_ONLY_ATR, false);
                } else
                {
                    return false;
                }
            } else
            {
                return false;
            }
        } catch (CoreException e)
        {
            Activator.getDefault().logError("Error determining if module " + module + " is read only.", e);
        }
        return false;

    }

    /**
     * Gets the current {@link Position} of the marker in the
     * {@link TLAEditor} showing the module that contains the
     * marker. Returns null if there is no editor open on that module.
     * This method assumes that {@link TLAEditor}s are synchronized. That
     * is, multiple editors on the same module are synchronized. At the time
     * of writing this method (June 2010), they are synchronized.
     * 
     * @param marker
     * @return
     */
    public static Position getMarkerPosition(IMarker marker)
    {
        TLAEditor editor = findTLAEditor(marker.getResource());
        if (editor != null)
        {
            IAnnotationModel annotationModel = editor.getDocumentProvider().getAnnotationModel(editor.getEditorInput());
            /*
             * From exploration of eclipse's code, I've determined that this
             * should be an instance of ResourceMarkerAnnotationModel. If this is
             * not always true, then we need to figure out a way to get a hold of the
             * annotation model that manages positions of markers in the editor.
             */
            if (annotationModel instanceof ResourceMarkerAnnotationModel)
            {
                return ((ResourceMarkerAnnotationModel) annotationModel).getMarkerPosition(marker);
            } else
            {
                Activator.getDefault().logDebug("Cannot get the annotation model that manages marker positions for the marker on "
                        + marker.getResource());
            }
        }

        return null;
    }

    /**
     * A class that we use so a method can return both a string and a 
     * location.
     * 
     * @author lamport
     *
     */
    public static final class StringAndLocation
    {
        public String string;
        public Location location;

        public StringAndLocation(String string, Location location)
        {
            this.string = string;
            this.location = location;

        }

        public String toString()
        {
            return "[string |-> " + this.string + ", location |-> " + this.location.toString() + "]";
        }
    }

	/**
	 * @param mapping
	 * @return
	 * @throws BadLocationException
	 */
	public static boolean selectAndRevealPCalRegionFromCurrentTLARegion() throws BadLocationException {

		final TLAtoPCalMapping mapping = getTLAEditorWithFocus().getTpMapping();
		if (mapping == null) {
			UIHelper.setStatusLineMessage("No valid TLA to PCal mapping found for current selection");
			return false;
		}

		final IDocument document = getCurrentDocument();
		final pcal.Region sourceRegion = AdapterFactory.jumptToPCal(mapping,
				EditorUtil.getCurrentLocation(1), document);
		if (sourceRegion == null) {
			// Cannot find a valid mapping for current selection
			return false;
		}

		/*
		 * The following command makes executing ReturnFromOpenDecl (F4) return
		 * to the selected location.
		 */
		setReturnFromOpenDecl();

		// Reveal the PCal source in the editor
		getTLAEditorWithFocus().selectAndReveal(sourceRegion);
		
		return true;
	}
}
