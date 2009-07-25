package org.lamport.tla.toolbox.tool.tlc.handlers;

import java.util.Iterator;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Repairs model launches
 * @author Simon Zambrovski
 * @version $Id$
 */
public class RepairLaunchHandler extends AbstractHandler
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
                            ModelHelper.recoverModel(config);
                        } 
                    } catch (CoreException e)
                    {
                        TLCUIActivator.logError("Error reparing the model launch", e);
                    }
                }
            }
        }
        return null;
    }
}
