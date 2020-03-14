package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.Iterator;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.tlc.model.Model;

/**
 * Stops model launches
 * @author Simon Zambrovski
 */
public class StopLaunchHandler extends AbstractHandler
{
    public static final String ID = "toolbox.tool.tlc.commands.model.stop";

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        ISelection selection = HandlerUtil.getCurrentSelection(event);
        if (selection instanceof IStructuredSelection && !((IStructuredSelection) selection).isEmpty())
        {
            IStructuredSelection structSelection = ((IStructuredSelection) selection);

            Iterator modelIterator = structSelection.iterator();
            while (modelIterator.hasNext())
            {
                Object element = modelIterator.next();
                if (element instanceof Model)
                {
                	Model model = (Model) element;
                    if (model.isRunning())
                    {
                        Job[] runningSpecJobs = Job.getJobManager().find(model.getLaunchConfiguration());
                        for (int i = 0; i < runningSpecJobs.length; i++)
                        {
                            // send cancellations to all jobs...
                            runningSpecJobs[i].cancel();
                        }
                    }
                }
            }
        }
        return null;
    }
}
