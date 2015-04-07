package org.lamport.tla.toolbox.spec;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IAdapterManager;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.jface.text.ITextSelection;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.compare.ResourceNameComparator;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

import pcal.TLAtoPCalMapping;
import tla2sany.modanalyzer.SpecObj;
import util.SimpleFilenameToStream;

/**
 * Represents a specification handle in the toolbox
 * 
 * In June 2010, LL added some fields by which handlers of different commands
 * could communicate with one another. I'm sure there's a more elegant way to do
 * this that involves another few levels of indirection, but I have the
 * old-fashioned belief that doing things the easy way and commenting what you
 * do is better than doing things the correct way that makes it impossible to
 * figure out what the hell is going on without learning yet another almost but
 * not quite completely undocumented Eclipse feature.
 * 
 * 
 * @version $Id$
 * @author Simon Zambrovski
 */
public class Spec implements IAdaptable {

    /**
     * specnames2mappings.get(filename) is the TLAtoPCalMapping object produced
     * by the PlusCal translator for the file named tpMappingNames[i], where the
     * file name is the module name + ".tla". (Sometimes it's easier to get the
     * file name, and sometimes the module name, and it's easier to add a ".tla"
     * than to remove it.)
     * <p>
     * There are two public procedures for manipulating these fields:
     * 
     * @see Spec#setTpMapping(TLAtoPCalMapping, String)
     * @see Spec#getTpMapping(String)
     */
    private final Map<String, TLAtoPCalMapping> spec2mappings = new HashMap<String, TLAtoPCalMapping>();

    /**
     * The following fields are used for remembering the jumping-off point for a
     * Goto Declaration or ShowDefinitions command, so we can return to it with
     * a Return from Goto Declaration command. They should probably be changed
     * to arrays so we can call return from a Sequence of such commands.
     */
    private String openDeclModuleName;
    private ITextSelection openDeclSelection;

    /**
     * The following fields are used to remember the result of a Show Uses
     * command so the Goto Next Use and Goto Previous Use commands know where to
     * go.
     * 
     * The name of the module whose instances are being shown. If there are more
     * than one, this is set by user selection from a pop-up dialog.
     */
    private String moduleToShow = null;

    /**
     * The markers to be shown, sorted by the locations in which they originally
     * appeared. I don't think that order can change, but what do I know?
     */
    private IMarker[] markersToShow = null;

    /**
     * The index of the marker in markersToShow that is currently being shown.
     */
    private int currentSelection = 0;

    /* project handle */
    private final IProject project;

    /* root module handle */
    private IFile rootFile;

    /* status of the specification */
    private int status;

    /* the semantic tree produced by the parser */
    private SpecObj specObj;

    /**
     * Creates a Spec handle for existing project. Use the factory method
     * {@link Spec#createNewSpec(String, String, Date)} if the project reference
     * is not available
     * 
     * @param project
     *            project handle
     */
    public Spec(IProject project) {
    	Assert.isNotNull(project);
        this.project = project;
        initProjectProperties();
    }

    /**
     * Factory method Creates a new specification, the underlying IProject link
     * the root file
     * 
     * @param name
     *            the name of the specification
     * @param rootFilename
     *            the path to the root file name
     * @param importExisting
     * 
     *            Note: when importing an existing spec, the contents of the
     *            .toolbox directory needs to be fixed because it contains
     *            absolute path names, which may be incorrect if the spec was
     *            moved from someplace else. Here are the files that may need
     *            changing:
     * 
     *            .toolbox/.project : <location> entries This definitely needs
     *            to be changed. .toolbox/.setting/... .prefs : ProjectRootFile
     *            entry. This file is rewritten when the spec is created, so it
     *            may not need to be changed.
     * 
     *            Experiment shows that the rootFilename argument contains the
     *            complete path name, from which one could extract the path
     *            names of those files and then rewrite them as needed.
     * @param monitor
     */
    public static Spec createNewSpec(String name, String rootFilename,
            boolean importExisting, IProgressMonitor monitor) {
        IProject project = ResourceHelper.getProject(name, rootFilename, true,
                importExisting, monitor);
        PreferenceStoreHelper.storeRootFilename(project, rootFilename);

        Spec spec = new Spec(project);
        spec.setLastModified();
        return spec;
    }

    /**
     * initializes the root module from the project properties
     */
    private void initProjectProperties() {
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
        // - Add a failed field to the Spec object, initialized to false
        // - Set this field to true when the error occurs.
        // After the statement
        //
        // spec = new Spec(projects[i]);
        //
        // in the constructor of WorkspaceSpecManager, test this field and,
        // if true, take the appropriate action--probably popping up a warning
        // (if that's possible) or else putting the name of the spec in the
        // log, and also probably not executing the addSpec command that follows
        // this statement.
        //
        if (this.rootFile == null) {
            Activator
                    .getDefault()
                    .logError(
                            "A spec did not load correctly, probably because it was modified outside the Toolbox."
                                    + "\n Error occurred in toolbox/spec/Spec.initProjectProperties()",
                            null);
        } else {
            // Initialize TLAtoPCalMapping here for the root module to have it
            // available the moment the user needs it the first time. This is
            // just an
            // optimization because the mapping would be looked up later
            // automatically, but has the advantage that it is not done on the
            // UI thread.
            this.getTpMapping(this.rootFile.getName());
        }
    }

    /**
     * @return the lastModified
     */
    public Date getLastModified() {
        if (IResource.NULL_STAMP == project.getModificationStamp()) {
            return null;
        }
        return new Date(project.getModificationStamp());
    }

    /**
     * Touches the underlying resource
     */
    public void setLastModified() {
        try {
            project.touch(new NullProgressMonitor());
        } catch (CoreException e) {
            Activator.getDefault().logError(
                    "Error changing the timestamp of the spec", e);
        }
    }

    /**
     * Retrieves the underlying project file
     * 
     * @return the project
     */
    public IProject getProject() {
        return project;
    }

    /**
     * @return the name
     */
    public String getName() {
        return project.getName();
    }

    /**
     * Retrieves the path to the file containing the root module This is a
     * convenience method for {@link getRootFile()#getLocation()#toOSString()}
     * 
     * @return the OS representation of the root file
     */
    public String getRootFilename() {
        IPath location = rootFile.getLocation();
        return location.toOSString();
    }

    /**
     * Retrieves the handle to the root file
     * 
     * @return IFile of the root
     */
    public IFile getRootFile() {
        return this.rootFile;
    }

    /**
     * Retrieves parsing status
     * 
     * See {@link IParseConstants} for possible values of status.
     * 
     * @return the status
     */
    public int getStatus() {
        return status;
    }

    /**
     * Sets parsing status. As a side effect the
     * {@link SpecLifecycleParticipant}s get informed
     * 
     * @param status
     *            the status to set
     */
    public void setStatus(int status) {
        this.status = status;
        // informs
        Activator.getSpecManager().specParsed(this);
    }

    /**
     * @see org.eclipse.core.runtime.IAdaptable#getAdapter(java.lang.Class)
     */
    public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
        // lookup the IAdapterManager service
        IAdapterManager manager = Platform.getAdapterManager();
        // forward the request to IAdapterManager service
        return manager.getAdapter(this, adapter);
    }

    /**
     * Retrieves the list of modules in the spec, or an empty list if no modules <br>
     * The list is sorted on the resource name
     * 
     * @return
     */
    public IResource[] getModuleResources() {
        // TODO relate this list to the list of modules, which result after
        // parse
        IResource[] modules = null;
        try {
            modules = getProject().members(IResource.NONE);
            // sort the markers
            List<IResource> moduleList = new ArrayList<IResource>(
                    Arrays.asList(modules));
            Collections.sort(moduleList, new ResourceNameComparator());
            return moduleList.toArray(new IResource[moduleList.size()]);

        } catch (CoreException e) {
            Activator.getDefault().logError(
                    "Error retrieving the the spec modules", e);
            modules = new IResource[0];
        }
        return modules;
    }

    /**
     * Returns the SpecObj
     */
    public SpecObj getRootModule() {
        return this.specObj;
    }

    /**
     * Returns the SpecObj only on valid status
     */
    public SpecObj getValidRootModule() {
        if (AdapterFactory.isProblemStatus(this.status)) {
            return null;
        }
        return getRootModule();

    }

    /**
     * Sets the new spec object
     * 
     * @param specObj
     */
    public void setSpecObj(SpecObj specObj) {
        this.specObj = specObj;
    }

    /**
     * @param openDeclModuleName
     *            the openDeclModuleName to set
     */
    public void setOpenDeclModuleName(String openDeclModuleName) {
        this.openDeclModuleName = openDeclModuleName;
    }

    /**
     * @return the openDeclModuleName
     */
    public String getOpenDeclModuleName() {
        return openDeclModuleName;
    }

    /**
     * @param openDeclSelection
     *            the openDeclSelection to set
     */
    public void setOpenDeclSelection(ITextSelection openDeclSelection) {
        this.openDeclSelection = openDeclSelection;
    }

    /**
     * @return the openDeclSelection
     */
    public ITextSelection getOpenDeclSelection() {
        return openDeclSelection;
    }

    /**
     * @param moduleToShow
     *            the moduleToShow to set
     */
    public void setModuleToShow(String moduleToShow) {
        this.moduleToShow = moduleToShow;
    }

    /**
     * @return the moduleToShow
     */
    public String getModuleToShow() {
        return moduleToShow;
    }

    /**
     * @param markersToShow
     *            the markersToShow to set
     */
    public void setMarkersToShow(IMarker[] markersToShow) {
        this.markersToShow = markersToShow;
    }

    /**
     * @return the markersToShow
     */
    public IMarker[] getMarkersToShow() {
        return markersToShow;
    }

    /**
     * @param currentSelection
     *            the currentSelection to set
     */
    public void setCurrentSelection(int currentSelection) {
        this.currentSelection = currentSelection;
    }

    /**
     * @return the currentSelection
     */
    public int getCurrentSelection() {
        return currentSelection;
    }

    /**
     * @see ResourceHelper#getTLALibraryPath(IProject)
     */
    public String[] getTLALibraryPath() {
    	return ResourceHelper.getTLALibraryPath(project);
    }

    /**
     * @return A {@link String} with all user defined TLA+ library path
     *         locations concatenated and as a Java VM {@link System} property.
     *         If the user has not set any library path locations, an empty
     *         {@link String} is returned, not <code>null</code>.
     * @see Spec#getTLALibraryPath()
     */
    public String getTLALibraryPathAsVMArg() {
        final String[] tlaLibraryPath = getTLALibraryPath();

        if (tlaLibraryPath.length > 0) {
            final StringBuffer buf = new StringBuffer(tlaLibraryPath.length * 2);

            buf.append("-D" + SimpleFilenameToStream.TLA_LIBRARY + "=");

            for (final String location : tlaLibraryPath) {
                buf.append(location);
                buf.append(File.pathSeparator);
            }

            final String vmArg = buf.toString();

            // remove dangling pathSeparator
            return vmArg.substring(0, vmArg.length() - 1);
        } else {
            return "";
        }
    }

    private final Lock lock = new ReentrantLock(true);

    /**
     * @param filename
     *            The filename of the {@link Spec} for which the
     *            {@link TLAtoPCalMapping} is asked for.
     * @return A {@link TLAtoPCalMapping} for the given {@link Spec}'s filename
     *         or <code>null</code> if no mapping exist.
     */
    public TLAtoPCalMapping getTpMapping(final String filename) {
        lock.lock();
        try {
            TLAtoPCalMapping mapping = spec2mappings.get(filename);
            // In-memory cache miss and thus try to read the mapping from its
            // disc
            // file. If there exists no disk file, we assume there has never
            // existed
            // a mapping.
            if (mapping == null) {
                mapping = ResourceHelper
                        .readTLAtoPCalMapping(project, filename);
                if (mapping == null) {
                    mapping = new NullTLAtoPCalMapping();
                }
                spec2mappings.put(filename, mapping);
            }

            // Always return null if the mapping maps to a NullTLAtoPCalMapping
            // as
            // our consumers expect null to indicate a non-existent mapping.
            if (mapping instanceof NullTLAtoPCalMapping) {
                return null;
            }
            return mapping;
        } finally {
            lock.unlock();
        }
    }

    /**
     * Associates the specified mapping with the specified filename (optional
     * operation). If the {@link Spec} previously contained a mapping for the
     * filename, the old mapping is replaced by the specified map.
     * 
     * @param mapping
     *            The {@link TLAtoPCalMapping} object for the given
     *            <tt>filename</tt>. <code>null</code>, will cause an
     *            {@link IllegalArgumentException}.
     * @param filename
     *            key with which the specified value is to be associated.
     *            <code>null</code>, will cause an
     *            {@link IllegalArgumentException}.
     * @param monitor
     *            A valid {@link IProgressMonitor}, <code>null</code>, will
     *            cause an {@link IllegalArgumentException}.
     * @return the previous value associated with <tt>filename</tt>, or
     *         <tt>null</tt> if there was no mapping for <tt>filename</tt>.
     * @throws NullPointerException
     *             if the specified key or value is null and this map does not
     *             permit null keys or values
     * @throws IllegalArgumentException
     *             if some property of the specified key or value prevents it
     *             from being stored in this map
     */
    public TLAtoPCalMapping setTpMapping(final TLAtoPCalMapping mapping,
            final String filename, final IProgressMonitor monitor) {

        // Safeguard against inproper use of this API
        if (mapping == null || filename == null || monitor == null) {
            throw new IllegalArgumentException();
        }

        lock.lock();
        try {
            final TLAtoPCalMapping oldMapping = spec2mappings.put(filename,
                    mapping);

            // Check if old and new mapping are identical to avoid disk flush.
            // This requires proper equals/hashcode in TLAtoPCalMapping and
            // nested.
            if (!mapping.equals(oldMapping)) {
                // Use a submonitor to show progress as well as failure
                final SubProgressMonitor subProgressMonitor = new SubProgressMonitor(
                        monitor, 1);
                subProgressMonitor
                        .setTaskName("Writing TLA+ to PCal mapping for "
                                + filename);
                // Eagerly flush mapping to its persistent disk storage
                // (overwriting
                // any previous mapping stored on disk). This is relatively
                // cheap
                // compared to how often a mapping is re-generated, but has the
                // advantage that the mapping doesn't get lost if the Toolbox
                // decides to
                // not shut down gracefully.
                try {
                    Assert.isTrue(ResourceHelper.writeTLAtoPCalMapping(project,
                            filename, mapping, subProgressMonitor));
                } finally {
                    subProgressMonitor.done();
                }
            }

            return oldMapping;
        } finally {
            lock.unlock();
        }
    }

    @SuppressWarnings("serial")
    private static class NullTLAtoPCalMapping extends TLAtoPCalMapping {
    }
}
