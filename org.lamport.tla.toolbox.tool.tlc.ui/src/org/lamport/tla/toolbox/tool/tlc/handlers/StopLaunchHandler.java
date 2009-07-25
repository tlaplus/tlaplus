package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.Iterator;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Stops model launches
 * @author Simon Zambrovski
 * @version $Id$
 */
public class StopLaunchHandler extends AbstractHandler
{

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
                if (element instanceof ILaunchConfiguration)
                {
                    ILaunchConfiguration config = (ILaunchConfiguration) element;
                    try
                    {
                        if (ModelHelper.isModelLocked(config) && !ModelHelper.isModelStale(config))
                        {
                            Job[] runningSpecJobs = Job.getJobManager().find(config);
                            for (int i = 0; i < runningSpecJobs.length; i++)
                            {
                                // send cancellations to all jobs...
                                runningSpecJobs[i].cancel();
                            }
                        } 
                    } catch (CoreException e)
                    {
                        TLCUIActivator.logError("Error stopping the model launch", e);
                    }
                }
            }
        }
        return null;
    }
}
