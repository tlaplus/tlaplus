package org.lamport.tla.toolbox.tool.tla2tex.handler;

import java.io.File;
import java.util.Vector;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceDialog;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.PreferencesUtil;
import org.lamport.tla.toolbox.tool.tla2tex.TLA2TeXActivator;
import org.lamport.tla.toolbox.tool.tla2tex.preference.ITLA2TeXPreferenceConstants;
import org.lamport.tla.toolbox.ui.handler.SaveDirtyEditorAbstractHandler;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2tex.TLA;
import tla2tex.TLA2TexException;

/**
 * This handler will attempt to run TLA2TeX on a module if a
 * TLAEditorAndPDFViewer is currently selected. It will load the pdf file in the
 * second tab of the viewer.
 * 
 * @author Daniel Ricketts
 */
public class ProducePDFHandler extends SaveDirtyEditorAbstractHandler {

	private final String TLA2TeX_Output_Extension = "pdf";

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands
	 * .ExecutionEvent)
	 */
	public Object execute(final ExecutionEvent event) {
		if (!saveDirtyEditor(event)) {
			return null;
		}

		final IPreferenceStore preferenceStore = TLA2TeXActivator.getDefault().getPreferenceStore();
		final boolean useEmbeddedViewer = preferenceStore.getBoolean(ITLA2TeXPreferenceConstants.EMBEDDED_VIEWER);
		final boolean osHandlesPDF = preferenceStore.getBoolean(ITLA2TeXPreferenceConstants.HAVE_OS_OPEN_PDF);
		
		final IEditorInput editorInput = activeEditor.getEditorInput();
		if (editorInput instanceof IFileEditorInput) {
			final IResource fileToTranslate = ((IFileEditorInput) editorInput).getFile();
			if ((fileToTranslate != null) && ResourceHelper.isModule(fileToTranslate)) {
				final AbstractPDFViewerRunnable pdfViewer;
				
				if (osHandlesPDF) {
					pdfViewer = new OperatingSystemPDFRunnable(this, activeEditor.getSite(), fileToTranslate);
				} else if (useEmbeddedViewer) {
					pdfViewer = new EmbeddedPDFViewerRunnable(this, activeEditor.getSite(), fileToTranslate);
				} else {
					pdfViewer = new StandalonePDFViewerRunnable(this, activeEditor.getSite(), fileToTranslate);
				}
				
				runPDFJob(pdfViewer, fileToTranslate);
			}
		}

		return null;
	}

	/**
	 * This method schedules a long running job that runs tla2tex on the file to
	 * translate and loads it in the browser that is part of the second tab of
	 * the tlaEditorAndPDFViewer.
	 * 
	 * It is done as a long running job so that the UI thread is not locked
	 * while tla2tex runs.
	 * 
	 * This handles any unrecoverable error in tla2tex translation and presents
	 * it to the user as an error message.
	 * 
	 * If the user has the pdf file in the .toolbox directory open in another
	 * program, then the toolbox will show a warning stating that the new pdf
	 * file could not be created. It will display the old, unmodified pdf file
	 * to the user.
	 * 
	 * @param tlaEditorAndPDFViewer
	 * @param fileToTranslate
	 */
	void runPDFJob(final AbstractPDFViewerRunnable runnable, final IResource fileToTranslate) {
		Job tla2TexJob = new WorkspaceJob("Produce PDF") {
			public IStatus runInWorkspace(final IProgressMonitor monitor) {
				try {
					final Vector<String> tla2texArgs = new Vector<String>();
					final IPreferenceStore preferenceStore = TLA2TeXActivator.getDefault().getPreferenceStore();

					if (preferenceStore
							.getBoolean(ITLA2TeXPreferenceConstants.SHADE_COMMENTS)) {
						tla2texArgs.add("-shade");
						tla2texArgs.add("-nops"); // The -nops switch added by
													// LL on 7 Apr 2010
					}

					if (preferenceStore
                            .getBoolean(ITLA2TeXPreferenceConstants.NO_PCAL_SHADE)) {
                        tla2texArgs.add("-noPcalShade");  
                    }

					if (preferenceStore
							.getBoolean(ITLA2TeXPreferenceConstants.NUMBER_LINES)) {
						tla2texArgs.add("-number");
					}

					tla2texArgs.add("-latexCommand");
					String latexCommand = preferenceStore
							.getString(ITLA2TeXPreferenceConstants.LATEX_COMMAND);
					tla2texArgs.add(latexCommand);

					tla2texArgs.add("-grayLevel");
					tla2texArgs
							.add(Double.toString(preferenceStore
									.getDouble(ITLA2TeXPreferenceConstants.GRAY_LEVEL)));

					tla2texArgs.add("-latexOutputExt");
					tla2texArgs.add(TLA2TeX_Output_Extension);
					tla2texArgs.add("-metadir");
					tla2texArgs.add(fileToTranslate.getProject().getLocation()
							.toOSString());
					tla2texArgs.add(fileToTranslate.getLocation().toOSString());

					// the two units of work are running
					// the translation and opening the pdf file
					// in the browser
					monitor.beginTask("Producing PDF", 2);
					monitor.subTask("Translating Module");

					TLA.runTranslation((String[]) tla2texArgs
							.toArray(new String[tla2texArgs.size()]));

					// Refresh the Eclipse workspace after a file has been
					// created outside of the Eclipse Resource realm. This makes
					// sure that the Eclipse resource layer sees the newly
					// created (PDF) file.
					// Without an explicit refresh, one might see the symptoms
					// outlined in Bug #317 in general/bugzilla/index.html
					// (org.eclipse.core.internal.resources.ResourceException:
					// Resource '/Test/Test.pdf' does not exist.)
					fileToTranslate.getProject().refreshLocal(IResource.DEPTH_INFINITE, monitor);

					monitor.worked(1);

					final String outputFileName = fileToTranslate.getProject()
							.getLocation().toOSString()
							+ File.separator
							+ ResourceHelper.getModuleName(fileToTranslate)
							+ "." + TLA2TeX_Output_Extension;
					
					final File outputFile = new File(outputFileName);
					if (outputFile.exists()) {
						
						runnable.setFile(outputFileName);
						runnable.setMonitor(monitor);
						
						// Open the file if it exists.
						// If it has not been modified, this is
						// most likely because it is open in an
						// external program, so display this information
						// to the user.
						UIHelper.runUISync(runnable);
					} else {
						final Runnable r = () -> {
							MessageDialog.openError(UIHelper.getShellProvider().getShell(), "PDF file not found",
									"Could not locate a pdf file for the module.");
						};
						
						UIHelper.runUIAsync(r);
					}
				} catch (final TLA2TexException | CoreException e) {
					handleJobException(e);
				}
				return Status.OK_STATUS;
			}
		};

		// setUser(false) to not popup a modal dialog on each PDF generation.
		tla2TexJob.setUser(false);
		tla2TexJob.setPriority(Job.LONG);
		tla2TexJob.schedule();
	}
	
	private void handleJobException(final Exception e) {
		TLA2TeXActivator.getDefault().logError("Error while producing pdf file: " + e.getMessage(), e);

		final Runnable r = () -> {
			final Shell s = PlatformUI.getWorkbench().getDisplay().getActiveShell();
			final int response = MessageDialog.open(MessageDialog.ERROR, s, "PDF Production Problem",
					"The following error was encountered while attempting to generate the PDF - perhaps you "
						+ "have not set a full path to pdflatex in the preferences?\n\n" + e.getMessage(),
					SWT.NONE, "Open Preferences", "Ok");
			
			if (response == 0) {
				final PreferenceDialog dialog = PreferencesUtil.createPreferenceDialogOn(s, 
						"toolbox.tool.tla2tex.preference.TLA2TeXPreferencePage",
						new String[] { "toolbox.tool.tla2tex.preference.TLA2TeXPreferencePage" }, null);
				dialog.open();
			}
		};
		
		UIHelper.runUIAsync(r);
	}
}
