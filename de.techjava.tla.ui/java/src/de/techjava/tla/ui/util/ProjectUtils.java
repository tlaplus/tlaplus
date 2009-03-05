package de.techjava.tla.ui.util;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.natures.TLANature;

/**
 * Toolbox for project support
 * 
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ProjectUtils.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class ProjectUtils 
{
    /**
     * Retrieves current project
     * @return
     */
	public static IProject getCurrentProject()
	{
		IEditorPart editor = UIPlugin.getDefault().getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
		IEditorInput input =  editor.getEditorInput();
		IFile file = null;
		if(input instanceof IFileEditorInput){
			file = ((IFileEditorInput)input).getFile();
		}
		if(file==null)
			return null;
		
		IProject project = file.getProject();
		
		return project;	
	}
	
	/**
	 * Retrieves project temp directory
	 * @param project
	 * @return
	 */
	public static String getProjectTempDir(IProject project)
	{
		IPath projecttempfolder = project.getLocation().makeAbsolute();
		projecttempfolder = projecttempfolder.append(".tla");
		if(!projecttempfolder.toFile().exists()){
			projecttempfolder.toFile().mkdirs();
		}
		return projecttempfolder.toOSString();
		
	}
	
	/**
	 * Retrieves project directory
	 * @param project
	 * @return
	 */
	public static String getProjectDir(IProject project)
	{
		IPath projectfolder = project.getLocation().makeAbsolute();;
		if(!projectfolder.toFile().exists()){
			projectfolder.toFile().mkdirs();
		}
		return projectfolder.toOSString();
	}

    /**
     * Create source and config directories if needed
     * @param project
     */
    public static void createDirectories(IProject project) 
    {
        IEclipsePreferences projectNode = getProjectNode(project);
    	if (projectNode != null) 
    	{

			boolean projectLayoutSeparatedValue = projectNode.getBoolean(ITLAProjectConstants.PERSIST_PROJECT_LAYOUT_SEPARATED, ITLAProjectConstants.DEFAULT_TLA_PROJECT_LAYOUT_SEPARATED);
		    IPath projectPath = project.getLocation().makeAbsolute();

			
			if (projectLayoutSeparatedValue)
			{
			    // create directories
			    String projectSourceValue = projectNode.get(ITLAProjectConstants.PERSIST_PROJECT_SOURCE_FOLDER, "");
			    String projectConfigValue = projectNode.get(ITLAProjectConstants.PERSIST_PROJECT_CONFIG_FOLDER, "");
			    
			    
			
			    IPath sourcePath = projectPath.addTrailingSeparator().append(projectSourceValue);
			    if (sourcePath.toFile() != null && !sourcePath.toFile().exists())
			    {
			        sourcePath.toFile().mkdirs();
			    }
			    IPath configPath = projectPath.addTrailingSeparator().append(projectConfigValue);
			    if (configPath.toFile() != null && !configPath.toFile().exists())
			    {
			        configPath.toFile().mkdirs();
			    }
			}
			
			String projectWorkingValue = projectNode.get(ITLAProjectConstants.PERSIST_PROJECT_WORKING_FOLDER, ITLAProjectConstants.DEFAULT_TLA_PROJECT_LAYOUT_WORKINGDIR);
		    IPath workingPath = projectPath.addTrailingSeparator().append(projectWorkingValue);
		    if (workingPath.toFile() != null && !workingPath.toFile().exists())
		    {
		        workingPath.toFile().mkdirs();
		    }

    	}
    }
    /**
     * Retrieves project preference node
     * @param project 
     * @return
     */
    public static IEclipsePreferences getProjectNode(IProject project)
    {
        ProjectScope scope = new ProjectScope(project);
        IEclipsePreferences projectNode = scope.getNode(UIPlugin.PLUGIN_ID);
        return projectNode;
    }
    /**
     * Adds TLA+ nature to the project
     * @param project project to add the nature to
     * @param monitor monitor to show progress
     * @throws CoreException
     */
    public static void addNatureToProject(IProject project, IProgressMonitor monitor) 
    	throws CoreException
    {
		IProjectDescription description = project.getDescription();
		
		String[] natures 	= description.getNatureIds();
		String[] newNatures = new String[natures.length + 1];
		
		System.arraycopy(natures, 0, newNatures, 1, natures.length);
		
		newNatures[0] = TLANature.NATURE_ID;
		description.setNatureIds(newNatures);
		project.setDescription(description, (monitor == null) ? null: new SubProgressMonitor(monitor, 1));
        
    }

    /**
     * Removes TLA+ Nature from project
     * @param project
     * @param object
     */
    public static void removeNatureFromProject(IProject project, IProgressMonitor monitor)
    	throws CoreException
    {
		IProjectDescription description = project.getDescription();
		
		String[] natures 	= description.getNatureIds();
		String[] newNatures = new String[natures.length - 1];
		
		for (int i = 0, j = 0; i < natures.length; i++) 
		{
		    if (!natures[i].equals(TLANature.NATURE_ID)) 
		    {
		        newNatures[j++] = natures[i];
		    }
		}
		description.setNatureIds(newNatures);
		project.setDescription(description, (monitor == null) ? null: new SubProgressMonitor(monitor, 1));
    }
}
