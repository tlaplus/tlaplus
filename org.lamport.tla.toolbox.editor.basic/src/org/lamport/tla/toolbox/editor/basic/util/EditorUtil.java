package org.lamport.tla.toolbox.editor.basic.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.TheoremNode;

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
            Activator.logError("Error setting module " + module + " to read only.", e);
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
            Activator.logError("Error determining if module " + module + " is read only.", e);
        }
        return false;

    }
}
