package org.lamport.tla.toolbox.spec;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
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
 * 
 * In June 2010, LL added some fields by which handlers of different commands
 * could communicate with one another.  I'm sure there's a more elegant way to
 * do this that involves another few levels of indirection, but I have the old-fashioned
 * belief that doing things the easy way and commenting what you do is better than
 * doing things the correct way that makes it impossible to figure out what
 * the hell is going on without learning yet another almost but not quite completely
 * undocumented Eclipse feature.
 * 
 * 
 * @version $Id$
 * @author Simon Zambrovski
 */
public class Spec implements IAdaptable
{

    /**
     *  The following fields are used for remembering the jumping-off
     *  point for a Goto Declaration or ShowDefinitions command, so we can return to it
     *  with a Return from Goto Declaration command.  They should probably
     *  be changed to arrays so we can call return from a Sequence of such commands.  
     */
    private String openDeclModuleName;
    private ITextSelection openDeclSelection;

    /**
     * The following fields are used to remember the result of a Show Uses command so
     * the Goto Next Use and Goto Previous Use commands know where to go.  
     *
     * The name of the module whose instances are being shown.  If there
     * are more than one, this is set by user selection from a pop-up 
     * dialog.
     */
    private String moduleToShow = null;

    /**
     * The markers to be shown, sorted by the locations in which they
     * originally appeared.  I don't think that order can change,
     * but what do I know?
     */
    private IMarker[] markersToShow = null;

    /**
     * The index of the marker in markersToShow that is currently being 
     * shown. 
     */
    private int currentSelection = 0;

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
     * 
     * Note: when importing an existing spec, the contents of the .toolbox directory needs to
     * be fixed because it contains absolute path names, which may be incorrect if the
     * spec was moved from someplace else.  Here are the files that seem to need changing:
     * 
     *    .toolbox/.project : <location> entries
     *    .toolbox/.setting/... .prefs  : ProjectRootFile entry.
     *    
     * Experiment shows that the rootFilename argument contains the complete path name,
     * from which one could extract the path names of those files and then rewrite them
     * as needed.
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

        // Assert.isNotNull(this.rootFile);
        // This assertion was preventing the Toolbox from starting, so LL
        // comented it out on 19 Mar 2011 and added the log message
        // on 3 Apr 2011.
        // To report this problem to the user, one can do the following:
        //   - Add a failed field to the Spec object, initialized to false
        //   - Set this field to true when the error occurs.
        // After the statement
        //
        //   spec = new Spec(projects[i]);
        //
        // in the constructor of WorkspaceSpecManager, test this field and,
        // if true, take the appropriate action--probably popping up a warning
        // (if that's possible) or else putting the name of the spec in the
        // log, and also probably not executing the addSpec command that follows
        // this statement.
        // 
        if (this.rootFile == null)
        {
            Activator.logError("A spec did not load correctly, probably because it was modified outside the Toolbox." +
                               "\n Error occurred in toolbox/spec/Spec.initProjectProperties()", null);
        }
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

    /**
     * @param moduleToShow the moduleToShow to set
     */
    public void setModuleToShow(String moduleToShow)
    {
        this.moduleToShow = moduleToShow;
    }

    /**
     * @return the moduleToShow
     */
    public String getModuleToShow()
    {
        return moduleToShow;
    }

    /**
     * @param markersToShow the markersToShow to set
     */
    public void setMarkersToShow(IMarker[] markersToShow)
    {
        this.markersToShow = markersToShow;
    }

    /**
     * @return the markersToShow
     */
    public IMarker[] getMarkersToShow()
    {
        return markersToShow;
    }

    /**
     * @param currentSelection the currentSelection to set
     */
    public void setCurrentSelection(int currentSelection)
    {
        this.currentSelection = currentSelection;
    }

    /**
     * @return the currentSelection
     */
    public int getCurrentSelection()
    {
        return currentSelection;
    }

}
