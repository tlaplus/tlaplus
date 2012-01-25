package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.ToolboxJob;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Triggers parsing of specification's root file
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParseSpecHandler extends AbstractHandler implements IHandler
{
    // TODO improve
    private IProgressMonitor monitor = new NullProgressMonitor();

    /**
     * @see IHandler#execute(ExecutionEvent event)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        // List references = UIHelper.checkOpenResources("Modified resources",
        // "Some resources are modified.\nDo you want to save the modified resources?");
        // for (int i = 0; i < references.size(); i++)
        // {
        // // save resources
        // // TODO!!!!
        // // ((EditorReference)references.get(i)).getEditor(false);
        // // saveDirtyEditors();
        // }

        // List editorReferences = UIHelper.getDirtyEditorReferences();
        // if (editorReferences.size() > 0)
        // {
        // boolean saveResources = UIHelper.promptUserForSave("Modified resources",
        // "Some resources are modified.\nDo you want to save the modified resources?");
        // if (saveResources)
        // {
        // UIHelper.saveResources(editorReferences);
        // }
        // }

        boolean proceed = UIHelper.promptUserForDirtyModules();

        if (!proceed)
        {
            return null;
        }

        final Spec spec = Activator.getSpecManager().getSpecLoaded();

        if (spec != null)
        {
            	Job job = new ToolboxJob("Parsing spec handler...") {
					@Override
					protected IStatus run(IProgressMonitor monitor) {
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
						return Status.OK_STATUS;
					}
            	};
            	job.schedule();
        } else
        {
            // TODO handle this case (could it occur?, declare in plugin.xml to activate the parse button on active
            // editor only)
        }
        return null;
    }

	/* (non-Javadoc)
	 * @see org.eclipse.core.commands.AbstractHandler#isEnabled()
	 */
	@Override
	public boolean isEnabled() {
		if (Activator.getSpecManager().getSpecLoaded() == null) {
			return false;
		}
		return super.isEnabled();
	}

    /**
     * @deprecated
     */
    protected void saveDirtyEditors()
    {
        Display display = UIHelper.getCurrentDisplay(); 
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
