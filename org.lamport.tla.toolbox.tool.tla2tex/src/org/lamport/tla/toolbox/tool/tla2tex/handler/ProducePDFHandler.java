package org.lamport.tla.toolbox.tool.tla2tex.handler;

import java.io.File;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.browser.ProgressEvent;
import org.eclipse.swt.browser.ProgressListener;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2tex.TLA;
import tla2tex.TLA2TexException;

/**
 * This handler will attempt to run TLA2TeX on a module if a TLAEditorAndPDFViewer is currently
 * selected. It will load the pdf file in the second tab of the viewer.
 * 
 * @author Daniel Ricketts
 * @version $Id$
 */
public class ProducePDFHandler extends AbstractHandler
{

    public Object execute(ExecutionEvent event)
    {

        IEditorPart activeEditor = UIHelper.getActivePage().getActiveEditor();

        if (activeEditor.isDirty())
        {
            // editor is not saved
            // TODO react on this!
        }

        IEditorInput editorInput = activeEditor.getEditorInput();
        if (editorInput instanceof IFileEditorInput)
        {
            final IResource fileToTranslate = ((IFileEditorInput) editorInput).getFile();
            if (fileToTranslate != null && ResourceHelper.isModule(fileToTranslate))
            {
                if (activeEditor instanceof TLAEditorAndPDFViewer)
                {
                    TLAEditorAndPDFViewer tlaEditorAndPDFViewer = (TLAEditorAndPDFViewer) activeEditor;

                    final Browser browser = tlaEditorAndPDFViewer.getPDFViewingPage().getBrowser();

                    // A progress listener is necessary because of the way a Browser widget works.
                    // When browser.setUrl or browser.setText is called, the code after that will continue
                    // executing regardless of whether that url or text has been loaded by the browser.
                    // Therefore, in order to ensure that the browser is not viewing the old pdf file
                    // when tla2tex is run, the code to run tla2tex is contained in the
                    // progressListener.completed method. This method is executed when a new url
                    // or string of html text is loaded. For this particular listener implemented
                    // below, this method will only be called when the html in
                    // browser.setText("<html><body>Producing PDF file...</body></html>"); is
                    // loaded. As soon as it is loaded, the browser removes this progress listener
                    // so that it is never called again. Then, tla2tex is run and the second tab in
                    // the multi page editor is set to the new pdf file.
                    ProgressListener progressListener = new ProgressListener() {

                        public void changed(ProgressEvent event)
                        {
                            // TODO Auto-generated method stub

                        }

                        public void completed(ProgressEvent event)
                        {
                            try
                            {
                                browser.removeProgressListener(this);
                                TLA.runTranslation(new String[] { "-latexCommand", "pdflatex", "-latexOutputExt",
                                        "pdf", "-metadir", fileToTranslate.getProject().getLocation().toOSString(),
                                        fileToTranslate.getLocation().toOSString() });
                                browser.setUrl((fileToTranslate.getProject().getLocation().toOSString()
                                        + File.separator + ResourceHelper.getModuleName(fileToTranslate) + ".pdf"));
                            } catch (TLA2TexException e)
                            {
                                Activator.logError("Error while producing pdf file: " + e.getMessage(), e);
                                MessageDialog.openError(UIHelper.getShellProvider().getShell(), "PDF Production Error",
                                        e.getMessage());

                            } finally
                            {

                            }
                        }
                    };
                    browser.addProgressListener(progressListener);

                    // It is necessary to navigate to this page in case a pdf file is already open.
                    // This allows tla2tex to write to that file before it gets displayed
                    // to the user again.
                    browser.setText("<html><body>Producing PDF file...</body></html>");

                }
            }
        }

        return null;
    }

}
