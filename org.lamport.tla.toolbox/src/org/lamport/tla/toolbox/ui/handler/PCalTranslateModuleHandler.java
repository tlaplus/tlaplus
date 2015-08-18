package org.lamport.tla.toolbox.ui.handler;

import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.commands.IHandler2;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.dialogs.ProgressMonitorDialog;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
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
public class PCalTranslateModuleHandler extends SaveDirtyEditorAbstractHandler implements IHandler, IHandler2
{
    public final static String COMMAND_ID = "toolbox.command.module.translate.active";

    /* (non-Javadoc)
     * @see org.eclipse.core.commands.AbstractHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
    	if (!saveDirtyEditor(event)) {
    		return null;
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
                // Changing the first argument of the following call to false
                // will make the translator run in the UI thread, making the UI
                // unresponsive while the translator is running.  However, it
                // might fix the Heisenbug that causes the translator to produce
                // a bogus "missing `begin'" error when run after fixing
                // a real error.  Or again, it might not.  
                // - Note added by LL on 2 Apr 2013
                // Note added by LL on 17 Aug 2015: 
                //  Changing the first argument apparently does not fix that bug.
                //  However, running the translator on the following algorithm
                //  reliably produces the bug:
                //
                //   (* --algorithm alok_test {
                //      {
                //        print "hello" 
                //        print "world"
                //    }
                //   } *)
                //
                //  Running the translator repeatedly on it switches between the
                // "missing ;" and the "missing `begin'" error.  After correcting
                //  the "missing ;" error, it reliably produces the "missing begin"
                //  error.  The translator behaves correctly when run from the
                // command line, so this is only a problem when the translator is
                // run from the Toolbox.
                //
                // This bug was fixed on 17 Aug 2015 by a change to ParseAlgorithm.java.
                //  
                progressDialog.run(true, false, translatorOperation);
                fileToBuild.refreshLocal(IResource.DEPTH_ONE, monitor);

            } catch (InvocationTargetException e)
            {
                Activator.getDefault().logError("Error during PlusCal Trnaslation", e);
            } catch (InterruptedException e)
            {
                Activator.getDefault().logError("Error during PlusCal Trnaslation", e);
            } catch (CoreException e)
            {
                Activator.getDefault().logError("Error during PlusCal Trnaslation", e);
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
