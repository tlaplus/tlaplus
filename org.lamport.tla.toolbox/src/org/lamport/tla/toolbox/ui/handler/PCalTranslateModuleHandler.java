package org.lamport.tla.toolbox.ui.handler;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.commands.IHandler2;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchWindow;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.job.TranslatorJob;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Triggers the PCal translation of the module
 * @author Simon Zambrovski
 * @version $Id$
 */
public class PCalTranslateModuleHandler extends AbstractHandler implements IHandler, IHandler2
{
    public final static String COMMAND_ID = "toolbox.command.module.translate.active";

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        final IEditorPart activeEditor = UIHelper.getActiveEditor();
        if (activeEditor.isDirty())
        {
            // editor is not saved just save it
            // TODO

			// Use NullProgressMonitor instead of newly created monitor. The
			// parent ProgressMonitorDialog would need to be properly
			// initialized first.
        	// @see https://bugzilla.tlaplus.net/show_activity.cgi?id=256
        	//
			// Generally though, saving a resource involves I/O which should be
			// decoupled from the UI thread in the first place. Properly doing
			// this, would be from inside a Job which provides a ProgressMonitor
            activeEditor.doSave(new NullProgressMonitor());
        }

        IEditorInput editorInput = activeEditor.getEditorInput();
        if (editorInput instanceof IFileEditorInput)
        {
            final IResource fileToBuild = ((IFileEditorInput) editorInput).getFile();

            IRunnableWithProgress translatorOperation = TranslatorJob.getAsRunnableWithProgress(fileToBuild);
            try
            {
                // Getting progress monitor
                final IWorkbenchWindow window = UIHelper.getActiveWindow();
                final Shell shell = (window != null) ? window.getShell() : null;
                final ProgressMonitorDialog progressDialog = new ProgressMonitorDialog(shell);
                final IProgressMonitor monitor = progressDialog.getProgressMonitor();
                progressDialog.run(true, false, translatorOperation);
                fileToBuild.refreshLocal(IResource.DEPTH_ONE, monitor);

            } catch (InvocationTargetException e)
            {
                Activator.logError("Error during PlusCal Trnaslation", e);
            } catch (InterruptedException e)
            {
                Activator.logError("Error during PlusCal Trnaslation", e);
            } catch (CoreException e)
            {
                Activator.logError("Error during PlusCal Trnaslation", e);
            }

            /*
                        TranslatorJob job = new TranslatorJob(fileToBuild);
                        job.setUser(true);
                        // TODO config file is also changed
                        job.setRule(getModifyRule(new IResource[]{fileToBuild}));
                        job.addJobChangeListener(new JobChangeAdapter(){
                            public void done(IJobChangeEvent event)
                            {
                                if (Status.OK_STATUS.equals(event.getResult()))
                                {
                                    try
                                    {
                                        fileToBuild.refreshLocal(IResource.DEPTH_ONE, null);
                                    } catch (CoreException e)
                                    {
                                        e.printStackTrace();
                                    }
                                }
                            }
                        });
                        job.schedule();
            */

        }
        return null;
    }
}
