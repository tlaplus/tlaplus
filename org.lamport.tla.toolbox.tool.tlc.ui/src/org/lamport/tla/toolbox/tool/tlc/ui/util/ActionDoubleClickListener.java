package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.st.Location;

/**
 * A listener that will respond to the user double clicking on
 * an action by opening the module containing that action and highlighting it.
 * 
 * Currently, double clicking on something in a viewer with this as
 * a listener will only do something if the selection is an instance
 * of {@link IModuleLocatable}.
 * {@link org.lamport.tla.toolbox.tool.tlc.output.data.TLCState} and
 * {@link org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformationItem}
 * implement that interface.
 * 
 * @author Daniel Ricketts
 *
 */
public class ActionDoubleClickListener implements IDoubleClickListener
{

    public void doubleClick(DoubleClickEvent event)
    {
        ISelection selection = event.getSelection();
        if (selection != null && !selection.isEmpty())
        {
            if (selection instanceof StructuredSelection)
            {
                StructuredSelection structuredSelection = (StructuredSelection) selection;
                // on a double click there should not be multiple selections,
                // so taking the first element of the structured selection
                // should work
                Object firstElement = structuredSelection.getFirstElement();
                if (firstElement instanceof IModuleLocatable)
                {
                    IModuleLocatable moduleLocatable = (IModuleLocatable) firstElement;
                    Location location = moduleLocatable.getModuleLocation();
                    if (location != null)
                    {
                        // the source of a location is the module name
                        IResource moduleResource = ResourceHelper.getResourceByModuleName(location.source());
                        if (moduleResource != null && moduleResource.exists())
                        {
                            try
                            {
                                // retrieve the resource
                                IDocument document = null;

                                // since we know that the editor uses file based editor representation
                                FileEditorInput fileEditorInput = new FileEditorInput((IFile) moduleResource);
                                FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();

                                fileDocumentProvider.connect(fileEditorInput);

                                document = fileDocumentProvider.getDocument(fileEditorInput);
                                if (document != null)
                                {
                                    try
                                    {
                                        // we now need to convert the four coordinates of the location
                                        // to a begin character location and a length

                                        // find the two lines in the document
                                        IRegion beginLineRegion = document.getLineInformation(location.beginLine() - 1);
                                        IRegion endLineRegion = document.getLineInformation(location.endLine() - 1);

                                        // get the text representation of the lines
                                        String textBeginLine = document.get(beginLineRegion.getOffset(),
                                                beginLineRegion.getLength());
                                        String textEndLine = document.get(endLineRegion.getOffset(), endLineRegion
                                                .getLength());

                                        // the Math.min is necessary because sometimes the end column
                                        // is greater than the length of the end line, so if Math.min
                                        // were not called in such a situation, extra lines would be
                                        // highlighted
                                        int actionStartPosition = beginLineRegion.getOffset()
                                                + Math.min(textBeginLine.length(), location.beginColumn() - 1);
                                        int length = endLineRegion.getOffset()
                                                + Math.min(textEndLine.length(), location.endColumn())
                                                - actionStartPosition;

                                        IEditorPart editor = UIHelper.openEditor(OpenSpecHandler.TLA_EDITOR_CURRENT,
                                                new FileEditorInput((IFile) moduleResource));

                                        if (editor != null && editor instanceof TLAEditorAndPDFViewer)
                                        {
                                            TLAEditorAndPDFViewer tlaEditorAndPDFViewer = (TLAEditorAndPDFViewer) editor;
                                            tlaEditorAndPDFViewer.getTLAEditor().selectAndReveal(actionStartPosition,
                                                    length);
                                        }
                                    } catch (BadLocationException e)
                                    {
                                        TLCUIActivator.logError("Error accessing the specified action location", e);
                                    }
                                }
                            } catch (CoreException e1)
                            {
                                TLCUIActivator.logDebug("Error going to action corresponding to state. This is a bug.");
                            }
                        }
                    }
                }
            }
        }
    }

}
