/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

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
import org.eclipse.jface.text.Position;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.part.MultiPageEditorPart;
import org.eclipse.ui.texteditor.ITextEditor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * @author lamport
 *
 */
public class GotoNextUseHandler extends AbstractHandler implements IHandler
{

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        Spec spec = ToolboxHandle.getCurrentSpec();
        if (spec == null)
        {
            // This should not happen.
            return null;
        }
        IMarker[] markers = spec.getMarkersToShow();
        if (markers == null)
        {
            // This should not happen.
            return null;
        }
        spec.setCurrentSelection((spec.getCurrentSelection() + 1) % markers.length);
        jumpToCurrentSelection(spec);

        return null;
    }

    public boolean isEnabled()
    {
        Spec spec = ToolboxHandle.getCurrentSpec();
        if (spec == null)
        {
            return false;
        }
        return spec.getMarkersToShow() != null;
    }

    /**
     * This method does the work of the Goto Next/Previous Use.  All the code in it was
     * copied from UIHelper.jumpToLocation.  This should be pulled out and made a 
     * method in UIHelper.  However, that's a nuisance because getting the offset and
     * length for the jump in jumpToLocation is performed deep inside that method. 
     *  
     * @param spec
     */
    public static void jumpToCurrentSelection(Spec spec)
    {
        IResource moduleResource = ResourceHelper.getResourceByModuleName(spec.getModuleToShow());
        if (moduleResource != null && moduleResource.exists())
        {
            /*
             * Now, retrieve a representation of the resource
             * as a document. To do this, we use a FileDocumentProvider.
             * 
             * We disconnect the document provider in the finally block
             * for the following try block in order to avoid a memory leak.
             */
            IDocument document = null;

            // since we know that the editor uses file based editor representation
            FileEditorInput fileEditorInput = new FileEditorInput((IFile) moduleResource);
            FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
            try
            {

                fileDocumentProvider.connect(fileEditorInput);

                document = fileDocumentProvider.getDocument(fileEditorInput);
                if (document != null)
                {
                    IMarker marker = spec.getMarkersToShow()[spec.getCurrentSelection()];
                    // The following gets the location information for the position at which
                    // the marker was created, not at its current position.  Is there any way
                    // to get the marker's current position?
                    // int offset = ((Integer) marker.getAttribute(IMarker.CHAR_START)).intValue();
                    // int length = ((Integer) marker.getAttribute(IMarker.CHAR_END)).intValue() - offset;
                    
                    // Yes.  Dan provided the following method and LL incorporated it into the
                    // code on 24 Jun 2010.
                    Position pos =EditorUtil.getMarkerPosition(marker);
                    int offset = pos.getOffset();
                    int length = pos.getLength();
                    
                    IEditorPart editor = UIHelper.openEditor(OpenSpecHandler.TLA_EDITOR_CURRENT, new FileEditorInput(
                            (IFile) moduleResource));

                    if (editor != null)
                    {
                        ITextEditor textEditor;

                        if (editor instanceof ITextEditor)
                        {
                            textEditor = (ITextEditor) editor;
                        } else
                        {

                            textEditor = (ITextEditor) editor.getAdapter(ITextEditor.class);
                        }

                        if (textEditor == null && editor instanceof MultiPageEditorPart)
                        {

                            IEditorPart[] editors = ((MultiPageEditorPart) editor).findEditors(editor.getEditorInput());
                            for (int i = 0; i < editors.length; i++)
                            {
                                if (editors[i] instanceof ITextEditor)
                                {
                                    textEditor = (ITextEditor) editors[i];
                                }
                            }
                        }

                        if (textEditor != null)
                        {
                            // the text editor may not be active, so set it active
                            if (editor instanceof MultiPageEditorPart)
                            {
                                ((MultiPageEditorPart) editor).setActiveEditor(textEditor);
                            }
                            // getActivePage().activate(textEditor);
                            textEditor.selectAndReveal(offset, length);
                        }
                    }

                }
            } catch (CoreException e1)
            {
                Activator.getDefault().logDebug("Error going to a module location. This is a bug.");
            } finally
            {
                fileDocumentProvider.disconnect(fileEditorInput);
            }
        }

    }

}
