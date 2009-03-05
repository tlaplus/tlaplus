package de.techjava.tla.ui.wizards;


import java.lang.reflect.InvocationTargetException;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IWorkspaceRoot;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.jface.operation.IRunnableWithProgress;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.dialogs.IOverwriteQuery;
import org.osgi.service.prefs.BackingStoreException;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.util.ITLAProjectConstants;
import de.techjava.tla.ui.util.ProjectUtils;


/**
 * Creates a project
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLANewProjectOperation.java,v 1.1 2005/08/22 15:43:35 szambrovski Exp $
 */
public class TLANewProjectOperation 
	implements IRunnableWithProgress 
{
	
	private TLANewProjectWizardPage[] 	pages;
	private IOverwriteQuery 			overwriteQuery;
	
	/**
	 * Constructor
	 * @param pages
	 * @param overwriteQuery
	 */
	public TLANewProjectOperation(TLANewProjectWizardPage[] pages, IOverwriteQuery overwriteQuery)
	{
		this.pages = pages;
		this.overwriteQuery = overwriteQuery;
	}


	/**
	 * @see org.eclipse.jface.operation.IRunnableWithProgress#run(org.eclipse.core.runtime.IProgressMonitor)
	 */
	public void run(IProgressMonitor monitor) 
		throws InvocationTargetException, InterruptedException 
	{
	if (monitor == null) {
			monitor= new NullProgressMonitor();
		}
		try {
			monitor.beginTask("Creating project", 2);
			IWorkspaceRoot root= UIPlugin.getWorkspace().getRoot();
			
			for (int i= 0; i < pages.length; i++) 
			{
				createProject(root, pages[i], new SubProgressMonitor(monitor, 1));
			}
		} finally {
			monitor.done();
		}
	}
	/**
	 * Creates a project
	 * @param root
	 * @param page
	 * @param monitor
	 * @throws InvocationTargetException
	 * @throws InterruptedException
	 */
	private void createProject(	IWorkspaceRoot root, 
	        					TLANewProjectWizardPage page, 
	        					IProgressMonitor monitor) 
		throws InvocationTargetException, InterruptedException 
	{
		
		monitor.beginTask("Creating Project Directory", 1);

		String name= page.getProjectName();
		try {
		    IProject project = root.getProject(name);
		if (!project.exists()) 
		{
		    project.create(null);
		}
		if (!project.isOpen()) 
		{
			project.open(null);
		}
	
		// Add nature
		ProjectUtils.addNatureToProject(project, monitor);
		
        String projectConfig = page.getConfigFolder();
        String projectSource = page.getSourceFolder();
        String projectWork   = page.getWorkingFolder();
        
        IPreferenceStore store = UIPlugin.getDefault().getPreferenceStore();

        IEclipsePreferences projectNode = ProjectUtils.getProjectNode(project);

        if (projectNode != null) 
    	{
    	    projectNode.putBoolean(ITLAProjectConstants.PERSIST_PROJECT_LAYOUT_SEPARATED, page.isSeparated());
    	    projectNode.put(ITLAProjectConstants.PERSIST_PROJECT_SOURCE_FOLDER, projectSource);
    	    projectNode.put(ITLAProjectConstants.PERSIST_PROJECT_CONFIG_FOLDER, projectConfig);
    	    projectNode.put(ITLAProjectConstants.PERSIST_PROJECT_WORKING_FOLDER, projectWork);
			ProjectUtils.createDirectories(project);
            projectNode.flush();
    	}

		project.refreshLocal(IProject.DEPTH_INFINITE, null);
			
		} catch (CoreException ce) 
		{
			throw new InvocationTargetException(ce);
		} catch (BackingStoreException bse) 
		{
			throw new InvocationTargetException(bse);

		}
		
	}

}
