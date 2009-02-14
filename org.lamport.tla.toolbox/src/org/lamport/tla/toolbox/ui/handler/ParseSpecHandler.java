package org.lamport.tla.toolbox.ui.handler;

import java.util.List;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Triggers parsing of specification's root file
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParseSpecHandler extends AbstractHandler implements IHandler
{
    // TODO provide the monitor
    private IProgressMonitor monitor = null;

    /**
     * @see IHandler#execute(ExecutionEvent event)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        List references = UIHelper.checkOpenResources("Modified resources",
                "Some resources are modified.\nDo you want to save the modified resources?");
        for (int i = 0; i < references.size(); i++)
        {
            // save resources
            // TODO!!!!
            // ((EditorReference)references.get(i)).getEditor(false);
            // saveDirtyEditors();
        }
        Spec spec = Activator.getSpecManager().getSpecLoaded();

        if (spec != null)
        {

            try
            {
                // this only cleans up
                spec.getProject().build(IncrementalProjectBuilder.CLEAN_BUILD, monitor);
                // this starts the build process
                spec.getProject().build(IncrementalProjectBuilder.FULL_BUILD, monitor);
            } catch (CoreException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }

        } else
        {
            // TODO handle this case (could it occur?, declare in plugin.xml to activate the parse button on active
            // editor only)
        }
        return null;
    }

    // TODO refine this...
    private void saveDirtyEditors()
    {
        Display display = Display.getCurrent();
        if (display == null)
            display = Display.getDefault();
        display.syncExec(new Runnable() {
            public void run()
            {
                IWorkbenchWindow[] windows = Activator.getDefault().getWorkbench().getWorkbenchWindows();
                for (int i = 0; i < windows.length; i++)
                {
                    IWorkbenchPage[] pages = windows[i].getPages();
                    for (int j = 0; j < pages.length; j++)
                        pages[j].saveAllEditors(false);
                }
            }
        });
    }

}
