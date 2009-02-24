package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.lamport.tla.toolbox.tool.tlc.job.AbstractJob;
import org.lamport.tla.toolbox.tool.tlc.job.TLCJob;

/**
 * Our sample handler extends AbstractHandler, an IHandler base class.
 * @see org.eclipse.core.commands.IHandler
 * @see org.eclipse.core.commands.AbstractHandler
 */
public class TLCLaunchHandler extends AbstractHandler
{
    /**
     * The constructor.
     */
    public TLCLaunchHandler()
    {
    }

    /**
     * the command has been executed, so extract extract the needed information
     * from the application context.
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {

        AbstractJob job = new TLCJob();
        job.addJobChangeListener(new JobChangeAdapter() 
        {

            public void done(IJobChangeEvent event)
            {
                if (event.getResult().isOK())
                {
                    System.out.println("JOB Change Listener ------------ { Done }");
                } else
                {
                    System.out.println("JOB Change Listener ------------ { Cancelled }");
                }
            }
        });
        job.setUser(true);
        job.schedule();
        return null;
    }
}
