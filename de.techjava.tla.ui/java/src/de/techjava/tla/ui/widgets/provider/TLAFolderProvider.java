package de.techjava.tla.ui.widgets.provider;

import java.util.Hashtable;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.ui.model.WorkbenchContentProvider;

import de.techjava.tla.ui.natures.TLANature;
import de.techjava.tla.ui.util.ITLAProjectConstants;
import de.techjava.tla.ui.util.ProjectUtils;

/**
 * Provides TLA Projects and Source Folders
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAFolderProvider.java,v 1.1 2005/08/22 15:43:37 szambrovski Exp $
 */
public class TLAFolderProvider 
	extends WorkbenchContentProvider 
{
    
    private Hashtable projectData = new Hashtable(50, 0.75f);
    private Hashtable fileExtData = new Hashtable(10, 0.75f);
    
    private boolean showSourceFolders;
    private boolean showConfigFolders;
    private boolean showWorkFolders;
    private boolean showAllFiles;
    
    /**
     * Constructor for TLAFile and Folder Provider
     * @param showSourceFolders if true source folders are shown
     * @param showConfigFolders if true config folders are shown
     * @param showWorkFolders if true work folders are shown
     * @param fileExtensions array containing list of file extension shown
     */
    public TLAFolderProvider(
            boolean showSourceFolders, 
            boolean showConfigFolders, 
            boolean showWorkFolders,
            String[] fileExtensions)
    {
        this.showSourceFolders 	= showSourceFolders;
        this.showConfigFolders 	= showConfigFolders;
        this.showWorkFolders 	= showWorkFolders;
        
        if (fileExtensions != null) 
        {
            for (int i=0; i < fileExtensions.length; i++)
            {
                fileExtData.put(fileExtensions[i],fileExtensions[i]);
            }
        } else {
            
            this.showAllFiles = true;
        }
    }
    /**
     * Constructor used for folder selection
     * the 
     * @param showSourceFolders
     * @param showConfigFolders
     * @param showWorkFolders
     */
    public TLAFolderProvider(
            boolean showSourceFolders, 
            boolean showConfigFolders, 
            boolean showWorkFolders)
    {
        this(showSourceFolders, showConfigFolders, showWorkFolders, null);
    }
    
    
    /**
     * @see org.eclipse.jface.viewers.ITreeContentProvider#getChildren(java.lang.Object)
     */
    public Object[] getChildren(Object element) 
    {
        Object[] children 		= super.getChildren(element); 
        Vector newChildren 		= new Vector(); 
        for (int i=0; i < children.length; i++)
        {
            Object child = children[i];
            if (child instanceof IProject) 
            {
                IProject project = (IProject) child;
                try 
                {
	                if (project.hasNature(TLANature.NATURE_ID))
	                {
	                    newChildren.add(project);
	                    cacheProject(project);
	                }
                } catch (CoreException ce) 
                {
                    
                }
            } else if (child instanceof IFolder) 
            {
                IFolder folder = (IFolder) child;
                IProject parent = folder.getProject();
                
                ProjectDataHolder holder = (ProjectDataHolder) projectData.get(parent);
                if (holder == null) 
                {
                    // this is strange
                    cacheProject(parent);
                    holder = (ProjectDataHolder) projectData.get(parent);
                }

                String folderPath = folder.getProjectRelativePath().toString();
                if (this.showConfigFolders && folderPath.equals(holder.getProjectConfig()))
                {
                    newChildren.add(folder);
                } 
                if (this.showSourceFolders && folderPath.equals(holder.getProjectSource()))
                {
                    newChildren.add(folder);
                }
                if (this.showWorkFolders && folderPath.equals(holder.getProjectWork()))
                {
                    newChildren.add(folder);
                }
                
            } else if (child instanceof IFile) 
            {
                IFile file = (IFile) child;
                String fileExtension = file.getProjectRelativePath().getFileExtension();
                if (this.showAllFiles || this.fileExtData.get(fileExtension) != null)
                {
                    newChildren.add(file);
                }
               
            }
            
        }
        
        return newChildren.toArray();
    }
    /**
     * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
     */
    public Object[] getElements(Object element) 
    {
        return getChildren(element);
    }
    /**
     * @see org.eclipse.jface.viewers.ITreeContentProvider#getParent(java.lang.Object)
     */
    public Object getParent(Object element) 
    {
        Object parent = super.getParent(element);
    
        return parent;
    }
    /**
     * @see org.eclipse.jface.viewers.ITreeContentProvider#hasChildren(java.lang.Object)
     */
    public boolean hasChildren(Object element) 
    {
        return getChildren(element).length > 0;
    }
    /**
     * Caches project information
     * @param project
     */
    private void cacheProject(IProject project)
    {
        if (projectData.get(project) != null) 
        {
            return;
        }
        
    	IEclipsePreferences projectNode = ProjectUtils.getProjectNode(project);
    	
    	if ( projectNode != null ) 
    	{
    		String projectSource 	= projectNode.get( ITLAProjectConstants.PERSIST_PROJECT_SOURCE_FOLDER, ITLAProjectConstants.DEFAULT_ROOT_FOLDER);
    		String projectConfig 	= projectNode.get( ITLAProjectConstants.PERSIST_PROJECT_CONFIG_FOLDER, ITLAProjectConstants.DEFAULT_ROOT_FOLDER);
    		String projectWork 		= projectNode.get( ITLAProjectConstants.PERSIST_PROJECT_WORKING_FOLDER, ITLAProjectConstants.DEFAULT_TLA_PROJECT_LAYOUT_WORKINGDIR);
    	
    		ProjectDataHolder holder = new ProjectDataHolder(project, projectSource, projectConfig, projectWork);
    		
    		projectData.put(project, holder);
    	}
    }
    
    
    
    /**
     * @see org.eclipse.jface.viewers.IContentProvider#dispose()
     */
    public void dispose() 
    {
        super.dispose();
        this.projectData = new Hashtable(50, 0.75f);
    }
    /**
     * Holder for project data
     * 
     * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
     * @version $Id: TLAFolderProvider.java,v 1.1 2005/08/22 15:43:37 szambrovski Exp $
     */
    private static class ProjectDataHolder
    {
        private IProject project;
        private String projectSource; 
        private String projectConfig; 
        private String projectWork;
        
        public ProjectDataHolder(IProject project, String projectSource, String projectConfig, String projectWork)
        {
            this.project 		= project;
            this.projectConfig 	= projectConfig;
            this.projectSource 	= projectSource;
            this.projectWork	= projectWork;
        }

        
        /**
         * @see java.lang.Object#equals(java.lang.Object)
         */
        public boolean equals(Object obj) 
        {
            return project.equals(((ProjectDataHolder)obj).getProject());
        }
        /**
         * @see java.lang.Object#hashCode()
         */
        public int hashCode() {
            return project.hashCode();
        }
        /**
         * @return Returns the project.
         */
        public IProject getProject() {
            return project;
        }
        /**
         * @return Returns the projectConfig.
         */
        public String getProjectConfig() {
            return projectConfig;
        }
        /**
         * @return Returns the projectSource.
         */
        public String getProjectSource() {
            return projectSource;
        }
        /**
         * @return Returns the projectWork.
         */
        public String getProjectWork() {
            return projectWork;
        }

    }
}

/*
 * $Log: TLAFolderProvider.java,v $
 * Revision 1.1  2005/08/22 15:43:37  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/10/25 16:49:44  sza
 * multiple file extension support
 *
 * Revision 1.1  2004/10/25 13:52:11  sza
 * *** empty log message ***
 *
 *
 */