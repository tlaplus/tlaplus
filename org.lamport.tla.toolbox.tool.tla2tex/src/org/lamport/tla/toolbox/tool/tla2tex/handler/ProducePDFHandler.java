package org.lamport.tla.toolbox.tool.tla2tex.handler;

import java.io.File;
import java.util.Vector;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.browser.ProgressEvent;
import org.eclipse.swt.browser.ProgressListener;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditorAndPDFViewer;
import org.lamport.tla.toolbox.tool.tla2tex.TLA2TeXActivator;
import org.lamport.tla.toolbox.tool.tla2tex.preference.ITLA2TeXPreferenceConstants;
import org.lamport.tla.toolbox.ui.handler.SaveDirtyEditorAbstractHandler;
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
public class ProducePDFHandler extends SaveDirtyEditorAbstractHandler
{

    private final String TLA2TeX_Output_Extension = "pdf";

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event)
    {
    	if (!saveDirtyEditor(event)) {
    		return null;
    	}
    	
        IEditorInput editorInput = activeEditor.getEditorInput();
        if (editorInput instanceof IFileEditorInput)
        {
            final IResource fileToTranslate = ((IFileEditorInput) editorInput).getFile();
            if (fileToTranslate != null && ResourceHelper.isModule(fileToTranslate))
            {
                if (activeEditor instanceof TLAEditorAndPDFViewer)
                {
                    final TLAEditorAndPDFViewer tlaEditorAndPDFViewer = (TLAEditorAndPDFViewer) activeEditor;

                    final Browser browser = tlaEditorAndPDFViewer.getPDFViewingPage().getBrowser();

                    if (browser != null)
                    {

                        // The browser has been instantiated because the pdf viewing page
                        // has been set active at some point in the past.

                        // A progress listener is necessary because of the way a Browser widget works.
                        // When browser.setUrl or browser.setText is called, the code after that will continue
                        // executing regardless of whether that url or text has been loaded by the browser.
                        // The page is loaded by the browser asynchronously.
                        // Therefore, in order to ensure that the browser is not viewing the old pdf file
                        // when tla2tex is run, the code to run tla2tex is contained in the
                        // progressListener.completed method. This method is executed when a new url
                        // or string of html text is loaded. For this particular listener implemented
                        // below, this method will only be called when the html in
                        // browser.setText("<html><body></body></html>"); is
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

                                browser.removeProgressListener(this);

                                // The following is performed as a job
                                // because producing running the tla2tex
                                // translation and navigating the browser
                                // to the new pdf can take several seconds.
                                // The job provides a progress monitor
                                // for the user and does not lock the UI thread.
                                // There are UI operations that must be performed
                                // within the job's run method. These must be
                                // run by calling UIHelper.runUISync.
                                runPDFJob(tlaEditorAndPDFViewer, fileToTranslate);

                            }
                        };

                        // The browser has already been created, so the pdf to be
                        // viewed may be loaded already. It is necessary to wait
                        // until a new page has been loaded before modifying
                        // the pdf.
                        browser.addProgressListener(progressListener);

                        // It is necessary to navigate to this page in case a pdf file is already open.
                        // This allows tla2tex to write to that file before it gets displayed
                        // to the user again.
                        browser.setText("<html><body></body></html>");
                    } else
                    {
                        // The browser has not yet been instantiated because
                        // the pdf viewing page has not been set active
                        // and multi page form editors only create the part
                        // control for a page when it is first set active.
                        // There is not need to worry about the browser being open on the pdf
                        // file, and the runPDFJob will set the pdf viewing page to
                        // be active which creates the browser widget.

                        // The following is performed as a job
                        // because producing running the tla2tex
                        // translation and navigating the browser
                        // to the new pdf can take several seconds.
                        // The job provides a progress monitor
                        // for the user and does not lock the UI thread.
                        // There are UI operations that must be performed
                        // within the job's run method. These must be
                        // run by calling UIHelper.runUISync.
                        runPDFJob(tlaEditorAndPDFViewer, fileToTranslate);
                    }

                }
            }
        }

        return null;
    }

    /**
     * This method schedules a long running job that runs tla2tex on the file to translate
     * and loads it in the browser that is part of the second tab of the tlaEditorAndPDFViewer.
     * 
     * It is done as a long running job so that the UI thread is not locked while tla2tex runs.
     * 
     * This handles any unrecoverable error in tla2tex translation and presents it to the user
     * as an error message.
     * 
     * If the user has the pdf file in the .toolbox directory open in another program, then
     * the toolbox will show a warning stating that the new pdf file could not be created. It
     * will display the old, unmodified pdf file to the user.
     * 
     * @param tlaEditorAndPDFViewer
     * @param fileToTranslate
     */
    private void runPDFJob(final TLAEditorAndPDFViewer tlaEditorAndPDFViewer, final IResource fileToTranslate)
    {
        Job tla2TexJob = new Job("Produce PDF") {

            protected IStatus run(final IProgressMonitor monitor)
            {

                try
                {

                    Vector tla2texArgs = new Vector();

                    IPreferenceStore preferenceStore = TLA2TeXActivator.getDefault().getPreferenceStore();

                    if (preferenceStore.getBoolean(ITLA2TeXPreferenceConstants.SHADE_COMMENTS))
                    {
                        tla2texArgs.add("-shade");
                        tla2texArgs.add("-nops");  // The -nops switch added by LL on 7 Apr 2010
                    }

                    if (preferenceStore.getBoolean(ITLA2TeXPreferenceConstants.NUMBER_LINES))
                    {
                        tla2texArgs.add("-number");
                    }

                    tla2texArgs.add("-latexCommand");
                    String latexCommand = preferenceStore.getString(ITLA2TeXPreferenceConstants.LATEX_COMMAND);
                    tla2texArgs.add(latexCommand);

                    tla2texArgs.add("-grayLevel");
                    tla2texArgs.add(Double.toString(preferenceStore.getDouble(ITLA2TeXPreferenceConstants.GRAY_LEVEL)));

                    tla2texArgs.add("-latexOutputExt");
                    tla2texArgs.add(TLA2TeX_Output_Extension);
                    tla2texArgs.add("-metadir");
                    tla2texArgs.add(fileToTranslate.getProject().getLocation().toOSString());
                    tla2texArgs.add(fileToTranslate.getLocation().toOSString());

                    // necessary for checking if the tla2tex output file is actually modified
                    // it will not be modified if it is open in an external program when
                    // of running tla2tex
                    final long translationStartTime = System.currentTimeMillis();

                    // the two units of work are running
                    // the translation and opening the pdf file
                    // in the browser
                    monitor.beginTask("Producing PDF", 2);
                    monitor.subTask("Translating Module");

                    TLA.runTranslation((String[]) tla2texArgs.toArray(new String[tla2texArgs.size()]));

                    monitor.worked(1);

                    final String outputFileName = fileToTranslate.getProject().getLocation().toOSString()
                            + File.separator + ResourceHelper.getModuleName(fileToTranslate) + "."
                            + TLA2TeX_Output_Extension;

                    final File outputFile = new File(outputFileName);
                    if (outputFile.exists())
                    {

                        // Open the file if it exists.
                        // If it has not been modified, this is
                        // most likely because it is open in an
                        // external program, so display this information
                        // to the user.
                        UIHelper.runUISync(new Runnable() {

                            public void run()
                            {
                                monitor.subTask("Opening PDF File");
                                tlaEditorAndPDFViewer.setActivePage(TLAEditorAndPDFViewer.PDFPage_ID);
                                tlaEditorAndPDFViewer.getPDFViewingPage().getBrowser().setUrl(outputFileName);
                                monitor.worked(1);

                                if (outputFile.lastModified() < translationStartTime)
                                {
                                    MessageDialog.openWarning(UIHelper.getShellProvider().getShell(),
                                            "PDF File Not Modified", "The pdf file could not be modified. "
                                                    + "Make sure that the file " + outputFileName
                                                    + " is not open in any external programs.");
                                }
                            }
                        });
                    } else
                    {
                        UIHelper.runUISync(new Runnable() {

                            public void run()
                            {
                                MessageDialog.openError(UIHelper.getShellProvider().getShell(), "PDF file not found",
                                        "Could not locate a pdf file for the module.");
                            }
                        });
                    }
                } catch (final TLA2TexException e)
                {
                    Activator.logError("Error while producing pdf file: " + e.getMessage(), e);
                    UIHelper.runUISync(new Runnable() {

                        public void run()
                        {
                            MessageDialog.openError(UIHelper.getShellProvider().getShell(), "PDF Production Error", e
                                    .getMessage());
                        }
                    });

                } finally
                {

                }
                return Status.OK_STATUS;
            }

        };

        tla2TexJob.setUser(true);
        tla2TexJob.setPriority(Job.LONG);
        tla2TexJob.schedule();
    }
}
