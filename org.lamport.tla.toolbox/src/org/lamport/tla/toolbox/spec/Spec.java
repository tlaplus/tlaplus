package org.lamport.tla.toolbox.spec;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IAdapterManager;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Platform;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.compare.ResourceNameComparator;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

import tla2sany.modanalyzer.SpecObj;

/**
 * Represents a specification handle in the toolbox
 * @version $Id$
 * @author Simon Zambrovski
 */
public class Spec implements IAdaptable
{

    /* project handle */
    private IProject project;

    /* root module handle */
    private IFile rootFile;

    /* status of the specification */
    private int status;

    /* the semantic tree produced by the parser */
    private SpecObj specObj;

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
        initProjectProperties();
    }

    /**
     * Factory method Creates a new specification, the underlying IProject link the root file
     * 
     * @param name the name of the specification
     * @param rootFilename the path to the root file name
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
    public void initProjectProperties()
    {
        this.rootFile = PreferenceStoreHelper.readProjectRootFile(project);
        this.specObj = null;
        this.status = IParseConstants.UNPARSED;
        
        Assert.isNotNull(this.rootFile);
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
        try
        {
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
     * This is a convenience method for {@link getRootFile()#getLocation()#toOSString()}
     * @return the OS representation of the root file
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
     * Retrieves the list of modules in the spec, or an empty list if no modules
     * <br>
     * The list is sorted on the resource name
     * 
     * @return
     */
    public IResource[] getModuleResources()
    {
        // TODO relate this list to the list of modules, which result after parse
        IResource[] modules = null;
        try
        {
            modules = getProject().members(IResource.NONE);
            // sort the markers
            List moduleList = new ArrayList(Arrays.asList(modules));
            Collections.sort(moduleList, new ResourceNameComparator());
            return (IResource[]) moduleList.toArray(new IResource[moduleList.size()]);

        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
            modules = new IResource[0];
        }
        return modules;
    }

    /**
     * Returns the SpecObj
     */
    public SpecObj getRootModule()
    {
        return this.specObj;
    }

    /**
     * Returns the SpecObj only on valid status
     */
    public SpecObj getValidRootModule()
    {
        if (AdapterFactory.isProblemStatus(this.status))
        {
            return null;
        }
        return getRootModule();
        
    }
    
    /**
     * Sets the new spec object
     * @param specObj
     */
    public void setSpecObj(SpecObj specObj)
    {
        this.specObj = specObj;
    }

    
}
