package org.lamport.tla.toolbox.tool.tlc.job;

import org.eclipse.core.runtime.jobs.Job;
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
    
    protected abstract Action getJobCompletedAction();

}
