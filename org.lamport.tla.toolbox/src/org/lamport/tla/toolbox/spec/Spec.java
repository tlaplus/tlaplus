package org.lamport.tla.toolbox.spec;

import java.util.Date;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IAdapterManager;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Platform;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.problem.ProblemContainer;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * Represents a specification handle in the toolbox
 * 
 * @author zambrovski
 */
public class Spec implements IAdaptable
{

    /* project handle */
    private IProject            project;

    /* root module handle */
    private IFile               rootFile;

    /* status of the specification */
    private int                 status                         = IParseConstants.UNPARSED;

    /* Problem container */
    private ProblemContainer    parseProblems;

    /**
     * Creates a Spec handle for existing project. Use the factory method
     * {@link Spec#createNewSpec(String, String, Date)} if the project reference is not available
     * 
     * @param project
     *            project handle
     */
    public Spec(IProject project)
    {
        this.project = project;
        this.parseProblems = new ProblemContainer();
        initProjectPropoerties();
    }

    /**
     * Factory method Creates a new specification, the underlying IProject link the root file
     * 
     * @param name
     * @param rootFilename
     * @param modified
     */
    public static Spec createNewSpec(String name, String rootFilename)
    {
        IProject project = ResourceHelper.getProject(name, rootFilename);

        PreferenceStoreHelper.storeRootFilename(project, rootFilename);

        Spec spec = new Spec(project);
        spec.setLastModified();
        return spec;
    }

    /**
     * initializes the root module from the project properties
     */
    public void initProjectPropoerties()
    {
        this.rootFile = PreferenceStoreHelper.readProjectRootFile(project);
    }

    /**
     * @return the lastModified
     */
    public Date getLastModified()
    {
        if (IResource.NULL_STAMP == project.getModificationStamp())
        {
            return null;
        }
        return new Date(project.getModificationStamp());
    }

    /**
     * Touches the underlying resource
     */
    public void setLastModified()
    {
        try {
            project.touch(null);
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    /**
     * Retrieves the underlying project file
     * 
     * @return the project
     */
    public IProject getProject()
    {
        return project;
    }

    /**
     * @return the name
     */
    public String getName()
    {
        return project.getName();
    }

    /**
     * Retrieves the path to the file containing the root module
     * 
     * @return
     */
    public String getRootFilename()
    {
        IPath location = rootFile.getLocation();
        return location.toOSString();

    }

    /**
     * Retrieves the handle to the root file
     * 
     * @return IFile of the root
     */
    public IFile getRootFile()
    {
        return this.rootFile;
    }

    /**
     * Retrieves parsing status
     * 
     * @return the status
     */
    public int getStatus()
    {
        return status;
    }

    /**
     * Sets parsing status
     * 
     * @param status
     *            the status to set
     */
    public void setStatus(int status)
    {
        this.status = status;
    }

    /**
     * Retrieves the problem container
     * 
     * @return the parseProblems
     */
    public ProblemContainer getParseProblems()
    {
        return parseProblems;
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.core.runtime.IAdaptable#getAdapter(java.lang.Class)
     */
    public Object getAdapter(Class adapter)
    {
        // lookup the IAdapterManager service
        IAdapterManager manager = Platform.getAdapterManager();
        // forward the request to IAdapterManager service
        return manager.getAdapter(this, adapter);
    }

    
    /**
     * @return the openedModules
     */
    public String[] getOpenedModules()
    {
        
        return PreferenceStoreHelper.getOpenedEditors(project);
    }

    /**
     * @param openedModules the openedModules to set
     */
    public void setOpenedModules(String[] openedModules)
    {
        PreferenceStoreHelper.storeOpenedEditors(project, openedModules);
    }

    /**
     * Retrieves the module with a given name belonging to the spec, or null, 
     * if the module can not be found (currently only root module is supported)
     *  
     * @param moduleName name of the module to retrieve
     * @return a valid IResouce or null
     */
    public IResource getModule(String moduleName)
    {
        if (moduleName == null) 
        {
            return null;
        }
        
        
        return ResourceHelper.getLinkedFile(getProject(), ResourceHelper.getModule(moduleName));
    }

}
