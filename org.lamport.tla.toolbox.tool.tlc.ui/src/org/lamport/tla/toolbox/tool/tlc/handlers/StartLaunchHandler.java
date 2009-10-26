package org.lamport.tla.toolbox.tool.tlc.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.handlers.HandlerUtil;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

/**
 * Runs a model
 * This class should no longer be used because the run
 * menu item in the spec explorer pop-up menu has been removed.
 * @author Simon Zambrovski
 * @deprecated
 * @version $Id$
 */
public class StartLaunchHandler extends AbstractHandler
{

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        ISelection selection = HandlerUtil.getCurrentSelection(event);
        if (selection instanceof IStructuredSelection && !((IStructuredSelection) selection).isEmpty())
        {
            Object element = ((IStructuredSelection) selection).getFirstElement();
            if (element instanceof ILaunchConfiguration)
            {
                ILaunchConfiguration config = (ILaunchConfiguration) element;
                try
                {
                    if (ModelHelper.isModelLocked(config) || ModelHelper.isModelStale(config))
                    {
                        return null;
                    }

                    ILaunch launch = config.launch(TLCModelLaunchDelegate.MODE_MODELCHECK, new NullProgressMonitor(),
                            false);
                    System.out.println("Launched " + launch + " is executed");
                } catch (CoreException e)
                {
                    TLCUIActivator.logError("Error launching the model", e);
                }
            }
        }
        return null;
    }
}
