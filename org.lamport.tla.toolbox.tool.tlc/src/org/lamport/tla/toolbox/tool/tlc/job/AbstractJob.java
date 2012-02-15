package org.lamport.tla.toolbox.tool.tlc.job;

import java.io.File;

import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jdt.internal.launching.StandardVMType;
import org.eclipse.jdt.launching.IVMInstall;
import org.eclipse.jdt.launching.IVMInstallType;
import org.eclipse.jdt.launching.JavaRuntime;
import org.eclipse.jface.action.Action;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.progress.IProgressConstants;

/**
 * General job
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class AbstractJob extends Job
{
    /**
     * 
     * @param name
     */
    public AbstractJob(String name)
    {
        super(name);
    }

    /**
     * 
     * @param job
     * @return
     */
    protected static boolean isModal(Job job)
    {
        Boolean isModal = (Boolean) job.getProperty(IProgressConstants.PROPERTY_IN_DIALOG);
        if (isModal == null)
            return false;
        return isModal.booleanValue();
    }

    /**
     * Called when the job is finished.
     */
    protected void doFinish()
    {
        // setProperty(IProgressConstants.ICON_PROPERTY, image);
        if (AbstractJob.isModal(this))
        {
            Display.getDefault().asyncExec(new Runnable() {
                public void run()
                {
                    getJobCompletedAction().run();
                }
            });
        } else
        {
            setProperty(IProgressConstants.KEEP_PROPERTY, Boolean.TRUE);
            setProperty(IProgressConstants.ACTION_PROPERTY, getJobCompletedAction());
        }
    }
    

	protected IVMInstall getVMInstall() {
        IVMInstall vmInstall = null;

		// Try using the very same VM the Toolbox is running with (e.g.
		// this avoids problems when the Toolbox runs with a 64bit VM, but
		// the nested VM is a 32bit one).
        final String javaHome = System.getProperty("java.home");
        if (javaHome != null) {
            final IVMInstallType installType = new StandardVMType();
            vmInstall = installType.createVMInstall("TLCModelCheckerNestedVM");
            vmInstall.setInstallLocation(new File(javaHome));
            return vmInstall;
        }

        // get OS default VM (determined by path) not necessarily the same
		// the toolbox is running with.
        return JavaRuntime.getDefaultVMInstall();
	}

    protected abstract Action getJobCompletedAction();

}
