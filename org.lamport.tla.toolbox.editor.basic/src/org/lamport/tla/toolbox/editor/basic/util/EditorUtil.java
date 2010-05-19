package org.lamport.tla.toolbox.editor.basic.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.spec.parser.ParseResultBroadcaster;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.TheoremNode;
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
     * Returns the {@link TLAEditor} with focus or null if
     * there is none.
     * 
     * @return
     */
    public static TLAEditor getTLAEditorWithFocus()
    {
        IEditorPart activeEditor = UIHelper.getActivePage().getActiveEditor();
        // activeEditor.getAdapter(ITexto)
        if (activeEditor instanceof TLAEditorAndPDFViewer)
        {
            TLAEditor editor = ((TLAEditorAndPDFViewer) activeEditor).getTLAEditor();
            if (editor != null && editor.getViewer().getTextWidget().isFocusControl())
            {
                return editor;
            }
        }

        return null;
    }

    /**
     * Returns a TLA editor on moduleFileName and opens it in a window if there isn't 
     * one already open.  It also gives the editor focus.
     * 
     * @param moduleFileName name of the module with .tla extension.
     * @return
     */
    public static TLAEditor openTLAEditor(String moduleFileName)
    {
        IResource module = ResourceHelper.getResourceByName(moduleFileName);
        if (module != null && module instanceof IFile)
        {
            IEditorPart editor = UIHelper.openEditor(TLAEditor.ID, (IFile) module);
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
        IFile file = ((FileEditorInput) editor.getEditorInput()).getFile();
        String moduleName = ResourceHelper.getModuleName(file);

        ParseResult parseResult = ResourceHelper.getValidParseResult(file);

        return ResourceHelper.getTheoremNodeWithCaret(parseResult, moduleName, textSelection, document);
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
}
