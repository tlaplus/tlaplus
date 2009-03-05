package de.techjava.tla.ui.actions;

import java.util.Iterator;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.natures.TLANature;
import de.techjava.tla.ui.util.ProjectUtils;

/**
 * Delegate executed from proxy on using Add TLA+ Action 
 * @see IWorkbenchWindowActionDelegate
 */
public class TLANatureActionDelegate
	implements IWorkbenchWindowActionDelegate 
{
	private IWorkbenchWindow 	window;
	private ISelection			selection;
    private static final String ACTION_PROJECT_NATURE_ADD 		= "de.techjava.tla.ui.actions.AddProjectNature";
    private static final String ACTION_PROJECT_NATURE_REMOVE 	= "de.techjava.tla.ui.actions.RemoveProjectNature";
	
	/**
	 * The constructor.
	 */
	public TLANatureActionDelegate() 
	{
	}

	/**
	 * The action has been activated. The argument of the
	 * method represents the 'real' action sitting
	 * in the workbench UI.
	 * @see IWorkbenchWindowActionDelegate#run
	 */
	public void run(IAction action) 
	{

	    if (action.getId().equals(ACTION_PROJECT_NATURE_ADD)) 
	    {
	        if (selection != null && !selection.isEmpty() && selection instanceof StructuredSelection) 
	        {
	            StructuredSelection stSelection = (StructuredSelection) selection;
	            Iterator i = stSelection.iterator();
	            
	            for (;i.hasNext();) 
	            {
	                Object child = i.next();
	                if (child instanceof IProject)
	                {
	                    IProject project = (IProject)child;
	                    try 
	                    {
                            if (!project.hasNature(TLANature.NATURE_ID))
                            {
                                System.out.print("Add nature");
                                ProjectUtils.addNatureToProject(project, null);
                            }
                            project.refreshLocal(IProject.DEPTH_INFINITE, null);
                        } catch (CoreException ce) 
                        {
                            UIPlugin.logError("Error accessing project nature", ce);
                        }
	                }
	            }
	        } 
	    } else if (action.getId().equals(ACTION_PROJECT_NATURE_REMOVE))
	    {
	        if (selection != null && !selection.isEmpty() && selection instanceof StructuredSelection) 
	        {
	            StructuredSelection stSelection = (StructuredSelection) selection;
	            Iterator i = stSelection.iterator();
	            
	            for (;i.hasNext();) 
	            {
	                Object child = i.next();
	                if (child instanceof IProject)
	                {
	                    IProject project = (IProject)child;
	                    try 
	                    {
                            if (project.hasNature(TLANature.NATURE_ID))
                            {
                                System.out.print("Remove nature");
                                ProjectUtils.removeNatureFromProject(project, null);
                            } 
                            project.refreshLocal(IProject.DEPTH_INFINITE, null);
                        } catch (CoreException ce) 
                        {
                            UIPlugin.logError("Error accessing project nature", ce);
                        }
	                }
	            }
	        } 
	        
	        
	    }
	    
	}

	/**
	 * Selection in the workbench has been changed. We 
	 * can change the state of the 'real' action here
	 * if we want, but this can only happen after 
	 * the delegate has been created.
	 * @see IWorkbenchWindowActionDelegate#selectionChanged
	 */
	public void selectionChanged(IAction action, ISelection selection) 
	{
	    this.selection = selection;
	}

	/**
	 * We can use this method to dispose of any system
	 * resources we previously allocated.
	 * @see IWorkbenchWindowActionDelegate#dispose
	 */
	public void dispose() 
	{
	}

	/**
	 * We will cache window object in order to
	 * be able to provide parent shell for the message dialog.
	 * @see IWorkbenchWindowActionDelegate#init
	 */
	public void init(IWorkbenchWindow window) 
	{
		this.window = window;
	}
}