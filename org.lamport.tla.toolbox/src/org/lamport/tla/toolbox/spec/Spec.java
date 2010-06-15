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
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.jface.text.ITextSelection;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;
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

    /**
     *  The following fields are used for remembering the jumping-off
     *  point for an Open Declaration or ShowDefinitions command, so we can return to it
     *  with a Return from Open Declaration command.  They should probably
     *  be changed to arrays so we can call return from a Sequence of such commands.  
     */
    private String openDeclModuleName;
    private ITextSelection openDeclSelection;
      
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
     * @param importExisting
     */
    public static Spec createNewSpec(String name, String rootFilename, boolean importExisting)
    {
        IProject project = ResourceHelper.getProject(name, rootFilename, true, importExisting);
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
        
        // Initialize the spec's ToolboxDirSize property.
        // Added by LL and Dan on 21 May 2010
        ResourceHelper.setToolboxDirSize(this.project);
        
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
            project.touch(new NullProgressMonitor());
        } catch (CoreException e)
        {
            Activator.logError("Error changing the timestamp of the spec", e);
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
     * See {@link IParseConstants} for possible values of status.
     * 
     * @return the status
     */
    public int getStatus()
    {
        return status;
    }

    /**
     * Sets parsing status. As a side effect the {@link SpecLifecycleParticipant}s get informed  
     * 
     * @param status the status to set
     */
    public void setStatus(int status)
    {
        this.status = status;
        // informs
        Activator.getSpecManager().specParsed(this);
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
            Activator.logError("Error retrieving the the spec modules", e);
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

    /**
     * @param openDeclModuleName the openDeclModuleName to set
     */
    public void setOpenDeclModuleName(String openDeclModuleName)
    {
        this.openDeclModuleName = openDeclModuleName;
    }

    /**
     * @return the openDeclModuleName
     */
    public String getOpenDeclModuleName()
    {
        return openDeclModuleName;
    }

    /**
     * @param openDeclSelection the openDeclSelection to set
     */
    public void setOpenDeclSelection(ITextSelection openDeclSelection)
    {
        this.openDeclSelection = openDeclSelection;
    }

    /**
     * @return the openDeclSelection
     */
    public ITextSelection getOpenDeclSelection()
    {
        return openDeclSelection;
    }

}
