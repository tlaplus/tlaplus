package org.lamport.tla.toolbox.tool.tla2tex.handler;

import java.io.File;
import java.util.Vector;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.browser.ProgressEvent;
import org.eclipse.swt.browser.ProgressListener;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.tool.tla2tex.TLA2TeXActivator;
import org.lamport.tla.toolbox.tool.tla2tex.preference.ITLA2TeXPreferenceConstants;
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

    private final String TLA2TeX_Output_Extension = "pdf";

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

                                Vector tla2texArgs = new Vector();

                                IPreferenceStore preferenceStore = TLA2TeXActivator.getDefault().getPreferenceStore();

                                if (preferenceStore.getBoolean(ITLA2TeXPreferenceConstants.SHADE_COMMENTS))
                                {
                                    tla2texArgs.add("-shade");
                                }

                                if (preferenceStore.getBoolean(ITLA2TeXPreferenceConstants.NUMBER_LINES))
                                {
                                    tla2texArgs.add("-number");
                                }

                                tla2texArgs.add("-latexCommand");
                                String latexCommand = preferenceStore
                                        .getString(ITLA2TeXPreferenceConstants.LATEX_COMMAND);
                                tla2texArgs.add(latexCommand);

                                tla2texArgs.add("-grayLevel");
                                tla2texArgs.add(Double.toString(preferenceStore
                                        .getDouble(ITLA2TeXPreferenceConstants.GRAY_LEVEL)));

                                tla2texArgs.add("-latexOutputExt");
                                tla2texArgs.add(TLA2TeX_Output_Extension);
                                tla2texArgs.add("-metadir");
                                tla2texArgs.add(fileToTranslate.getProject().getLocation().toOSString());
                                tla2texArgs.add(fileToTranslate.getLocation().toOSString());

                                // necessary for checking if the tla2tex output file is actually modified
                                // it will not be modified if it is open in an external program when
                                // of running tla2tex
                                long translationStartTime = System.currentTimeMillis();

                                TLA.runTranslation((String[]) tla2texArgs.toArray(new String[tla2texArgs.size()]));

                                String outputFileName = fileToTranslate.getProject().getLocation().toOSString()
                                        + File.separator + ResourceHelper.getModuleName(fileToTranslate) + "."
                                        + TLA2TeX_Output_Extension;

                                File outputFile = new File(outputFileName);
                                if (outputFile.exists())
                                {

                                    browser.setUrl(outputFileName);

                                    if (outputFile.lastModified() < translationStartTime)
                                    {
                                        MessageDialog.openWarning(UIHelper.getShellProvider().getShell(),
                                                "PDF File Not Modified", "The pdf file could not be modified. "
                                                        + "Make sure that the file " + outputFileName
                                                        + " is not open in any external programs.");
                                    }
                                } else
                                {
                                    MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                                            "PDF file not found", "Could not locate a pdf file for the module.");
                                }
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
