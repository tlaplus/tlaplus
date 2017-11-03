package org.lamport.tla.toolbox.util;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InvalidClassException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Vector;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceRuleFactory;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.MultiRule;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.progress.UIJob;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.job.NewTLAModuleCreationOperation;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.nature.PCalDetectingBuilder;
import org.lamport.tla.toolbox.spec.nature.TLANature;
import org.lamport.tla.toolbox.spec.nature.TLAParsingBuilder;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.spec.parser.ParseResultBroadcaster;
import org.lamport.tla.toolbox.spec.parser.ParserDependencyStorage;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.ui.preference.EditorPreferencePage;
import org.lamport.tla.toolbox.ui.preference.LibraryPathComposite;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

import pcal.TLAtoPCalMapping;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.ParseException;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParser;
import tla2sany.parser.TLAplusParserConstants;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.DefStepNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.InstanceNode;
import tla2sany.semantic.LeafProofNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NewSymbNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tla2sany.semantic.UseOrHideNode;
import tla2sany.st.Location;
import tla2sany.st.SyntaxTreeConstants;
import util.FilenameToStream;
import util.UniqueString;

/**
 * A toolbox with resource related methods
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResourceHelper
{

    /**
     * Filename suffix for {@link TLAtoPCalMapping} files
     */
    private static final String PMAP_SUFFIX = ".pmap";
	/**
     * 
     */
    private static final String PROJECT_DESCRIPTION_FILE = ".project";
    /**
     * 
     */
    private static final String TOOLBOX_DIRECTORY_SUFFIX = ".toolbox";

    /**
     * TLA extension
     */
    public static final String TLA_EXTENSION = "tla";

    /*
     * Constants used for displaying modification history.
     * It has the syntax:
     *   modificationHistory +
     *   (lastModified + date + modifiedBy +
     *      username + newline)*
     *      
     * Note: The StringHelper.newline string wasn't being found on my 64-bit
     * Windows 7 machine.  So on 8 Dec 2010 I removed it from here, and added
     * a "\n" before it when writing a new file.
     */
    public static String modificationHistory = /* StringHelper.newline + */ "\\* Modification History";

    public static String lastModified = StringHelper.newline + "\\* Last modified ";

    public static String modifiedBy = " by ";

    /**
     * Look up if a project exist and return true if so
     * @param name name of the project
     * @return
     */
    public static boolean peekProject(String name, String rootFilename)
    {
        String root = getParentDirName(rootFilename);
        if (root == null)
        {
            return false;
        }
        File projectDir = new File(root.concat("/").concat(name).concat(TOOLBOX_DIRECTORY_SUFFIX));
        return projectDir.exists();
    }

    /**
     * Retrieves a resource in the current project (the one of current loaded spec) 
     * @param name name of the module (no extension)
     * @return IResource if found or <code>null</code>
     */
    public static IResource getResourceByModuleName(String name)
    {
        return getResourceByName(getModuleFileName(name));
    }

    /**
     * Retrieves a resource in the current project (the one of current loaded spec) 
     * @param name name of the resource
     * @return IResource if found or <code>null</code>
     */
    public static IResource getResourceByName(String name)
    {
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec != null)
        {
            IProject project = spec.getProject();
            return getLinkedFile(project, name, false);
        }
        return null;
    }

    /**
     * Retrieves the project handle
     * @param name name of the project
     * @return a project handle
     */
    public static IProject getProject(String name)
    {
        if (name == null)
        {
            return null;
        }
        IWorkspace ws = ResourcesPlugin.getWorkspace();
        IProject project = ws.getRoot().getProject(name);

        return project;
    }

    /**
     * Retrieves a project by name or creates a new project is <code>createMissing</code> is set to <code>true</code>
     * @param name name of the project, should not be null
     * @param rootFilename path to the root filename, should not be null
     * @param createMissing a boolean flag if a missing project should be created 
     * @param monitor a ProgressMonitor to report progress and cancellation 
     * @return a working IProject instance or null if project not at place and createMissing was false
     * 
     * <br><b>Note:</b> If the project does not exist in workspace it will be created, based
     * on the specified name and the path of the rootFilename. <br>The location (directory) of 
     * the project will be constructed as 
     * the parent directory of the rootFile + specified name + ".toolbox". 
     * <br>Eg. calling <tt>getProject("for", "c:/bar/bar.tla")</tt>
     * will cause the creation of the project (iff this does not exist) with location
     * <tt>"c:/bar/foo.toolbox"</tt>
     * @throws CoreException 
     * 
     */
    public static IProject getProject(String name, String rootFilename, boolean createMissing, boolean importExisting, IProgressMonitor monitor) throws CoreException
    {
    	Assert.isNotNull(name);
    	Assert.isNotNull(rootFilename);
    	
        IProject project = getProject(name);

        // create a project
        if (!project.exists() && createMissing)
        {
                String parentDirectory = getParentDirName(rootFilename);

                Assert.isNotNull(parentDirectory);

                // parent directory could be determined

                IPath projectDescriptionPath = new Path(parentDirectory).removeTrailingSeparator().append(
                        name.concat(TOOLBOX_DIRECTORY_SUFFIX)).addTrailingSeparator();

                // create a new description for the given name
                IProjectDescription description;

                boolean performImport = importExisting
                        && projectDescriptionPath.append(PROJECT_DESCRIPTION_FILE).toFile().exists();

                // there exists a project description file
                if (performImport)
                {
                    description = project.getWorkspace().loadProjectDescription(
                            projectDescriptionPath.append(PROJECT_DESCRIPTION_FILE));

                    // check the natures and install if missing
                    String[] natureIds = description.getNatureIds();
                    boolean natureFound = false;
                    for (int i = 0; i < natureIds.length; i++)
                    {
                        if (TLANature.ID.equals(natureIds[i]))
                        {
                            natureFound = true;
                            break;
                        }
                    }
                    if (!natureFound)
                    {
                        String[] newNatureIds = new String[natureIds.length + 1];
                        System.arraycopy(natureIds, 0, newNatureIds, 0, natureIds.length);
                        newNatureIds[natureIds.length] = TLANature.ID;
                        description.setNatureIds(newNatureIds);
                    }

                    // check builders and install if missing
                    ICommand[] commands = description.getBuildSpec();
                    boolean tlaBuilderFound = false;
                    boolean pcalBuilderFound = false;
                    int numberOfBuildersToInstall = 2;

                    for (int i = 0; i < commands.length; ++i)
                    {
                        String builderName = commands[i].getBuilderName();
                        if (builderName.equals(TLAParsingBuilder.BUILDER_ID))
                        {
                            tlaBuilderFound = true;
                            numberOfBuildersToInstall--;
                        } else if (builderName.equals(PCalDetectingBuilder.BUILDER_ID))
                        {
                            pcalBuilderFound = true;
                            numberOfBuildersToInstall--;
                        }

                        if (tlaBuilderFound && pcalBuilderFound)
                        {
                            break;
                        }
                    }

                    if (numberOfBuildersToInstall > 0)
                    {
                        ICommand[] newCommands = new ICommand[commands.length + numberOfBuildersToInstall];
                        System.arraycopy(commands, 0, newCommands, 0, commands.length);

                        int position = commands.length;

                        if (!tlaBuilderFound)
                        {
                            ICommand command = description.newCommand();
                            command.setBuilderName(TLAParsingBuilder.BUILDER_ID);
                            newCommands[position] = command;
                            position++;
                        }
                        if (!pcalBuilderFound)
                        {
                            ICommand command = description.newCommand();
                            command.setBuilderName(PCalDetectingBuilder.BUILDER_ID);
                            newCommands[position] = command;
                        }
                    }
                } else
                {
                    // create new description
                    description = project.getWorkspace().newProjectDescription(name);
                    description.setLocation(projectDescriptionPath);

                    // set TLA+ feature
                    description.setNatureIds(new String[] { TLANature.ID });

                    // set TLA+ Parsing Builder
                    ICommand command = description.newCommand();
                    command.setBuilderName(TLAParsingBuilder.BUILDER_ID);
                    // set PCal detecting builder
                    ICommand command2 = description.newCommand();
                    command2.setBuilderName(PCalDetectingBuilder.BUILDER_ID);

                    // setup the builders
                    description.setBuildSpec(new ICommand[] { command, command2 });
                }

                // create the project
                project.create(description, monitor);
                // refresh
                project.refreshLocal(IResource.DEPTH_INFINITE, monitor);

                // open the project
                project.open(monitor);

                // relocate files (fix the links)
                if (performImport)
                {
                    relocateFiles(project, new Path(parentDirectory), monitor);
                }
        }

        return project;

    }

    /**
     * Retrieves a a resource from the project, creates a link if createNew is true and the file is not present 
     * TODO improve this, if the name is wrong
     * 
     * @param name full filename of the resource
     * @param project
     * @param createNew, a boolean flag indicating if the new link should be created if it does not exist
     */
    public static IFile getLinkedFile(IContainer project, String name, boolean createNew)
    {
        if (name == null || project == null)
        {
            return null;
        }
        IPath location = new Path(name);
        IFile file = project.getFile(new Path(location.lastSegment()));
        if (createNew)
        {
            if (!file.isLinked())
            {
                try
                {
                    file.createLink(location, IResource.NONE, new NullProgressMonitor());
                    return file;

                } catch (CoreException e)
                {
                    Activator.getDefault().logError("Error creating resource link to " + name, e);
                }
            }
            if (file.exists())
            {
                return file;
            } else
            {
                return null;
            }
        }
        return file;
    }

    public static IFile getLinkedFileUnchecked(IContainer project, String name, boolean createNew) throws CoreException
    {
        if (name == null || project == null)
        {
            return null;
        }
        IPath location = new Path(name);
        IFile file = project.getFile(new Path(location.lastSegment()));
        if (createNew)
        {
            if (!file.isLinked())
            {
                    file.createLink(location, IResource.NONE, new NullProgressMonitor());
                    return file;
            }
            if (file.exists())
            {
                return file;
            } else
            {
                return null;
            }
        }
        return file;
    }

    /**
     * On relocation, all linked files in the project become invalid. This method fixes this issue
     * @param project project containing links to the non-existing files
     * @param newLocationParent the parent directory, where the files are located
     */
    private static void relocateFiles(IProject project, IPath newLocationParent, IProgressMonitor monitor)
    {
        Assert.isNotNull(project);
        Assert.isNotNull(newLocationParent);

        if (!newLocationParent.hasTrailingSeparator())
        {
            newLocationParent.addTrailingSeparator();
        }


        try
        {
        	final Map<IResource, IPath> failures = new HashMap<IResource, IPath>();
            IResource[] members = project.members();

            monitor.beginTask("Relocating Files", members.length * 2);

            for (int i = 0; i < members.length; i++)
            {
				final IResource resource = members[i];
				if (resource.isLinked() && (!resource.isAccessible() || resource.getRawLocation().isAbsolute())) {
                    // the linked file points to a file that does not exist.
                    String name = members[i].getName();
                    IPath newLocation = newLocationParent.append(name);
                    
                    members[i].delete(true, new SubProgressMonitor(monitor, 1));
                    if (newLocation.toFile().exists())
                    {
                        getLinkedFile(project, ResourceHelper.PARENT_ONE_PROJECT_LOC + name, true);
                        monitor.worked(1);

                        Activator.getDefault().logDebug("File found " + newLocation.toOSString());
                    } else
                    {
                    	failures.put(members[i], newLocation);
						Activator.getDefault().logError("Error relocating files in " + project.getName(), new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Error relocating file "
                                + name + ". The specified location " + newLocation.toOSString()
                                + " did not contain the file.")));
                    }
                } else
                {
                    monitor.worked(2);
                }

            }
            if (!failures.isEmpty()) {
        		
        		// Inform the user that the Toolbox failed to "relocate" files (we are going to call it
        		// "find" though, in hope that it's more meaningful).
        		// 
        		final StringBuffer buf = new StringBuffer(failures.size());
				buf.append(String.format("The Toolbox failed to find %s %s while opening the %s spec:",
						failures.size(), failures.size() > 1 ? "files" : "file", project.getName()));
				buf.append("\n\n");

				// Use the standard resolver to try and resolve the missing file. If it resolves
				// successfully, we assume it is a standard module. Note, that there is still the
				// possibility that the user decided to overwrite the standard module. In this
				// case, TLC will use the wrong version. Thus, still inform the user about what
				// we have done here.
				final FilenameToStream resolver = new RCPNameToFileIStream(
						getTLALibraryPath(project));
        		for (Entry<IResource, IPath> entry : failures.entrySet()) {
        			final String moduleName = entry.getKey().getName();
        			
        			// resolve and check if the File object really exists
        			final File resolve = resolver.resolve(moduleName, false);
					boolean assumedStandardModule = resolve.exists();
        			
					final String path = entry.getValue().toOSString();
					buf.append(String.format("%s %s", path, assumedStandardModule == true ? "(standard module)" : ""));
        			buf.append("\n\n");
        		}
				buf.append("Files marked as standard modules will not cause the spec parser to fail. "
						+ "If you intended to provide an overwrite of a standard module, it is up to you now to provide the module.\n"
						+ "Missing user modules will result in a parser failure and have to be manually created.");

        		// Finally raise a warning dialog showing the user what we have done to her spec. 
        		final UIJob job = new UIJob("Warning relocating files") {
        			@Override
        			public IStatus runInUIThread(IProgressMonitor monitor) {
						MessageDialog.openWarning(UIHelper.getShell(),
								String.format("Failed to find %s spec files!", failures.size(), failures.size() > 1 ? "files" : "file"), buf.toString());
        				return Status.OK_STATUS;
        			}
        		};
        		job.schedule();
        	}
        } catch (CoreException e)
        {
            Activator.getDefault().logError("Error relocating files in " + project.getName(), e);
        } finally
        {
            monitor.done();
        }
    }
    

    /**
     * Modified by LL on 28 Nov 2012 to make locationList a Vector instead of a
     * HashSet. With a HashSet, it returned the library paths in an order that
     * was mostly independent of the order of the paths specified by the user.
     * 
     * @return an Array of {@link String}s each set by the user as additional
     *         TLA+ library lookup path locations. Returns and empty array if
     *         none set, not <code>null</code>.
     */
    public static String[] getTLALibraryPath(final IProject project) {
        final IPreferenceStore store = PreferenceStoreHelper
                .getProjectPreferenceStore(project);

        // Read project specific and general preferences (project take
        // precedence over general ones)
        String prefStr = store
                .getString(LibraryPathComposite.LIBRARY_PATH_LOCATION_PREFIX);
        if ("".equals(prefStr)) {
            prefStr = PreferenceStoreHelper.getInstancePreferenceStore()
                    .getString(
                            LibraryPathComposite.LIBRARY_PATH_LOCATION_PREFIX);
        }

        if (!"".equals(prefStr)) {
            // final Set<String> locationList = new HashSet<String>();
            final Vector<String> locationList = new Vector<String>();
            // convert UI string into an array
            final String[] locations = prefStr
                    .split(LibraryPathComposite.ESCAPE_REGEX
                            + LibraryPathComposite.LOCATION_DELIM);
            for (String location : locations) {
                final String[] split = location
                        .split(LibraryPathComposite.ESCAPE_REGEX
                                + LibraryPathComposite.STATE_DELIM);
                if (Boolean.parseBoolean(split[1])) {
                    locationList.add(split[0]);
                }
            }
            return locationList.toArray(new String[locationList.size()]);
        }
        return new String[0];
    }

    /**
     * Retrieves a a resource from the project, creates a link, if the file is not present 
     * convenience method for getLinkedFile(project, name, true)  
     */
    public static IFile getLinkedFile(IProject project, String name)
    {
        return getLinkedFile(project, name, true);
    }

    /**
     * Retrieves the path of the parent directory
     * @param path
     *            path of the module
     * @return path of the container
     */
    public static String getParentDirName(String path)
    {
        return new File(path).getParent();
    }

    /**
     * See {@link ResourceHelper#getParentDirName(String)}
     */
    public static String getParentDirName(IResource resource)
    {
        if (resource == null)
        {
            return null;
        }
        return getParentDirName(resource.getLocation().toOSString());
    }

    /**
     * Return the ModuleNode for the module named moduleName,
     * if one exists from the last time the spec was parsed.
     * Otherwise, it returns null.
     * 
     * There is no guarantee that this ModuleNode bears any
     * relation to the current state of the module's .tla
     * file.
     * @param moduleName
     * @return
     */
    public static ModuleNode getModuleNode(String moduleName)
    {
        SpecObj specObj = ToolboxHandle.getSpecObj();
        if (specObj == null)
        {
            return null;
        }
        return specObj.getExternalModuleTable().getModuleNode(UniqueString.uniqueStringOf(moduleName));
    }

    /**
     * Retrieves the name of the module (filename without extension).
     * And what is it retrieving it from: the name of the modulefrom the name of the module.
     * That's really helpful documentation, Simon.
     * 
     * @param moduleFilename
     *            filename of a module
     * @return module name, if the specified file exists of null, if the specified file does not exist
     */
    public static String getModuleName(String moduleFilename)
    {
        return getModuleNameChecked(moduleFilename, true);
    }

    /**
     * See {@link ResourceHelper#getModuleName(String)}
     */
    public static String getModuleName(IResource resource)
    {
        if (resource == null)
        {
            return null;
        }
        return getModuleName(resource.getLocation().toOSString());
    }

    /**
     * Retrieves the name of the module (filename without extension)
     * 
     * @param moduleFilename
     *            filename of a module
     * @param checkExistence
     *            if true, the method returns module name, iff the specified file exists or null, if the specified file
     *            does not exist, if false - only string manipulations are executed
     * @return module name
     */
    public static String getModuleNameChecked(String moduleFilename, boolean checkExistence)
    {
        File f = new File(moduleFilename);
        IPath path = new Path(f.getName()).removeFileExtension();
        // String modulename = f.getName().substring(0, f.getName().lastIndexOf("."));
        if (checkExistence)
        {
            return (f.exists()) ? path.toOSString() : null;
        }
        return path.toOSString();
    }

    /**
     * Creates a module name from a file name (currently, only adding .tla extension)
     * 
     * @param moduleName
     *            name of the module
     * @return resource name
     */
    public static String getModuleFileName(String moduleName)
    {
        if (moduleName == null || moduleName.equals(""))
        {
            return null;
        } else
        {
            return moduleName.concat(".").concat(TLA_EXTENSION);
        }
    }

	/**
	 * Returns IFile handles to user module overrides. Let moduleFile be Foo.tla and its 
	 * corresponding folder contain to files Foo.class and Foo.java, the IFile[] will
	 * contain two handles to Foo.class and Foo.java.
	 */
	public static IFile[] getModuleOverrides(final IProject project, final IFile moduleFile) {
		final int indexOfFileExtension = moduleFile.getFileExtension().length() + 1;
		final String moduleName = moduleFile.getName().substring(0, moduleFile.getName().length() - indexOfFileExtension);

		final List<IFile> res = new ArrayList<IFile>();
		final String[] extensions = new String[] { ".class", ".java" };
		for (final String extension : extensions) {
			try {
				IFile userModuleOverride = ResourceHelper.getLinkedFileUnchecked(project,
						ResourceHelper.PARENT_ONE_PROJECT_LOC + moduleName + extension, true);
				if (userModuleOverride != null && userModuleOverride.exists()) {
					res.add(userModuleOverride);
				}
			} catch (CoreException ignoredOnPurpose) {
			}
		}
		return res.toArray(new IFile[0]);
	}

    /**
     * Determines if the given member is a TLA+ module
     * @param resource
     * @return
     */
    public static boolean isModule(IResource resource)
    {
        return (resource != null && TLA_EXTENSION.equals(resource.getFileExtension()));

    }

    /**
     * Creates a simple content for a new TLA+ module
     *  
     * @param moduleFileName, name of the file 
     * @return the stream with content
     */
    public static StringBuffer getEmptyModuleContent(String moduleFilename)
    {
        StringBuffer buffer = new StringBuffer();
        String moduleName = ResourceHelper.getModuleNameChecked(moduleFilename, false);
        int numberOfDashes = Math.max(4, (Activator.getDefault().getPreferenceStore().getInt(
                EditorPreferencePage.EDITOR_RIGHT_MARGIN)
                - moduleName.length() - 9) / 2);
        String dashes = StringHelper.copyString("-", numberOfDashes);
        buffer.append(dashes).append(" MODULE ").append(moduleName).append(" ").append(dashes).append(
                StringHelper.copyString(StringHelper.newline, 3));
        return buffer;
    }

    /**
     * Returns the content for the end of the module
     * @return
     */
    public static StringBuffer getModuleClosingTag()
    {
        StringBuffer buffer = new StringBuffer();
        buffer.append(
                StringHelper.copyString("=", Activator.getDefault().getPreferenceStore().getInt(
                        EditorPreferencePage.EDITOR_RIGHT_MARGIN))).append("\n"+modificationHistory).append(
                StringHelper.newline).append("\\* Created ").append(new Date()).append(" by ").append(
                System.getProperty("user.name")).append(StringHelper.newline);
        return buffer;
    }

    /**
     * Returns the content for the end of the module
     * @return
     */
    public static StringBuffer getConfigClosingTag()
    {
        StringBuffer buffer = new StringBuffer();
        buffer.append("\\* Generated on ").append(new Date());
        return buffer;
    }

    /**
     * Creates a simple content for a new TLA+ module
     *  
     * @param moduleFileName, name of the file 
     * @return the stream with content
     */
    public static StringBuffer getExtendingModuleContent(String moduleFilename, String extendedModuleName)
    {
        StringBuffer buffer = new StringBuffer();
        buffer.append("---- MODULE ").append(ResourceHelper.getModuleNameChecked(moduleFilename, false)).append(
                " ----\n").append("EXTENDS ").append(extendedModuleName).append("\n\n");
        return buffer;
    }

    /**
     * Checks, whether the module is the root file of loaded spec
     * @param module the 
     * @return
     */
    public static boolean isRoot(IFile module)
    {
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec == null)
        {
            return false;
        }
        return spec.getRootFile().equals(module);
    }

    /**
     * Constructs qualified name
     * @param localName
     * @return
     */
    public static QualifiedName getQName(String localName)
    {
        return new QualifiedName(Activator.PLUGIN_ID, localName);
    }

    /**
     * @param rootNamePath
     * @return
     */
    public static IWorkspaceRunnable createTLAModuleCreationOperation(IPath rootNamePath)
    {
        return new NewTLAModuleCreationOperation(rootNamePath);
    }

    /**
     * Writes contents stored in the string buffer to the file, replacing the content 
     * @param file
     * @param buffer
     * @param monitor
     * @throws CoreException
     */
    public static void replaceContent(IFile file, StringBuffer buffer, IProgressMonitor monitor) throws CoreException
    {
        ByteArrayInputStream stream = new ByteArrayInputStream(buffer.toString().getBytes());
        if (file.exists())
        {
            file.setContents(stream, IResource.FORCE, monitor);
        } else
        {
            throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Exected " + file.getName()
                    + " file has been removed externally"));
            // this will create a file in a wrong location
            // instead of /rootfile-dir/file.cfg it will create it under /specdir/file.cfg
            // file.create(stream, force, monitor);
        }
    }

    /**
     * Writes contents stored in the string buffer to the file, appending the content
     * @param file
     * @param buffer
     * @param monitor
     * @throws CoreException
     */
    public static void addContent(IFile file, StringBuffer buffer, IProgressMonitor monitor) throws CoreException
    {
        boolean force = true;
        ByteArrayInputStream stream = new ByteArrayInputStream(buffer.toString().getBytes());
        if (file.exists())
        {
            file.appendContents(stream, IResource.FORCE, monitor);
        } else
        {
            file.create(stream, force, monitor);
        }
    }

    /**
     * Retrieves a combined rule for modifying the resources
     * @param resources set of resources
     * @return a combined rule
     */
    public static ISchedulingRule getModifyRule(IResource[] resources)
    {
        if (resources == null)
        {
            return null;
        }
        ISchedulingRule combinedRule = null;
        IResourceRuleFactory ruleFactory = ResourcesPlugin.getWorkspace().getRuleFactory();
        for (int i = 0; i < resources.length; i++)
        {
            // if one of the resources does not exist
            // something is screwed up
            if (resources[i] == null || !resources[i].exists())
            {
                return null;
            }
            ISchedulingRule rule = ruleFactory.modifyRule(resources[i]);
            combinedRule = MultiRule.combine(rule, combinedRule);
        }
        return combinedRule;
    }

    public static ISchedulingRule getCreateRule(IResource resource)
    {
        IResourceRuleFactory ruleFactory = ResourcesPlugin.getWorkspace().getRuleFactory();
        return ruleFactory.createRule(resource);
    }

    /**
     * Retrieves a rule for modifying a resource
     * @param resource
     * @return
     */
    public static ISchedulingRule getModifyRule(IResource resource)
    {
        IResourceRuleFactory ruleFactory = ResourcesPlugin.getWorkspace().getRuleFactory();
        ISchedulingRule rule = ruleFactory.modifyRule(resource);
        return rule;
    }

    /**
     * Retrieves a combined rule for deleting resource
     * @param resource
     * @return
     */
    public static ISchedulingRule getDeleteRule(IResource[] resources)
    {
        if (resources == null)
        {
            return null;
        }
        ISchedulingRule combinedRule = null;
        IResourceRuleFactory ruleFactory = ResourcesPlugin.getWorkspace().getRuleFactory();
        for (int i = 0; i < resources.length; i++)
        {
            ISchedulingRule rule = ruleFactory.deleteRule(resources[i]);
            combinedRule = MultiRule.combine(rule, combinedRule);
        }
        return combinedRule;
    }

    /**
     * Retrieves a combined rule for creating resource
     * @param resource
     * @return
     */
    public static ISchedulingRule getCreateRule(IResource[] resources)
    {
        if (resources == null)
        {
            return null;
        }
        ISchedulingRule combinedRule = null;
        IResourceRuleFactory ruleFactory = ResourcesPlugin.getWorkspace().getRuleFactory();
        for (int i = 0; i < resources.length; i++)
        {
            ISchedulingRule rule = ruleFactory.createRule(resources[i]);
            combinedRule = MultiRule.combine(rule, combinedRule);
        }
        return combinedRule;
    }

    /**
	 * Renames and moves the project, but does not delete the old project. It's
	 * the callee's reponsibility.
	 * 
	 * @param project
	 * @param aNewName
	 */
    public static IProject projectRename(final IProject project, final String aNewName, final IProgressMonitor aMonitor)
    {
        try
        {
        	// move the project location to the new location and name
            final IProjectDescription description = project.getDescription();
            final IPath basePath = description.getLocation().removeLastSegments(1).removeTrailingSeparator();
			final IPath newPath = basePath.append(aNewName.concat(TOOLBOX_DIRECTORY_SUFFIX)).addTrailingSeparator();
            description.setLocation(newPath);
            description.setName(aNewName);

            // refresh the project prior to moving to make sure the fs and resource fw are in sync
        	project.refreshLocal(IResource.DEPTH_INFINITE, aMonitor);
            
        	project.copy(description, IResource.NONE | IResource.SHALLOW, aMonitor);
            
            return ResourcesPlugin.getWorkspace().getRoot().getProject(aNewName);
        } catch (CoreException e)
        {
            Activator.getDefault().logError("Error renaming a specification", e);
        }
        return null;
    }
    
    public static IProject refreshProject(final IProject aProject, final IProgressMonitor aMonitor) { 
    	try {
			aProject.refreshLocal(IResource.DEPTH_INFINITE, aMonitor);
		} catch (CoreException e) {
            Activator.getDefault().logError("Error refreshing a specification", e);
		}
    	return aProject;
    }

    /**
     * @param aSpec a {@link Spec} that should be refreshed.
     * @param aMonitor
     * @return The underlying project refreshed
     */
    public static IProject refreshSpec(final Spec aSpec, final IProgressMonitor aMonitor) {
    	return refreshProject(getProject(aSpec.getName()), aMonitor);
    }
    
    /**
	 * Deletes the project
	 * 
	 * The boolean argument isForget was added by LL on 3 August 2011. It is
	 * true iff the Toolbox should only remove the spec from its list of specs
	 * but should not delete its .toolbox directory.
	 * 
	 * @param project
	 *            the project to be deleted
	 * @param aMonitor
	 *            a monitor to track deletion progress
	 * @param isForget
	 *            indicates if the underlying project files should be deleted
	 *            from the file system. false to delete fs files, true otherwise
	 */
    public static void deleteProject(final IProject project, final IProgressMonitor aMonitor, boolean isForget)
    {
        try
        {
			if (isForget) {
				// This statement deletes the spec but not the .toolbox
				// directory
				project.delete(IResource.NEVER_DELETE_PROJECT_CONTENT, aMonitor);
			} else {
				// This statement deletes the spec and the .toolbox directory
				project.delete(true, aMonitor);
			}
            
        } catch (CoreException e)
        {
            Activator.getDefault().logError("Error deleting a specification", e);
        }
    }

    /**
     * If file has been parsed since it was last written, then return
     * its parseResult.  Else, return null.
     * @param file
     * @return
     */
    public static ParseResult getValidParseResult(IFile file)
    {

        ParseResult parseResult = ParseResultBroadcaster.getParseResultBroadcaster().getParseResult(file.getLocation());
        if ((parseResult == null))
        {
            return null;
        }

        long timeWhenParsed = parseResult.getParserCalled();
        long timeWhenWritten = file.getLocalTimeStamp();
        if ((timeWhenWritten == IResource.NULL_STAMP) || (timeWhenWritten > timeWhenParsed))
        {
            return null;
        }
        return parseResult;
    }

    /**
     * If parseResult's status is not equal to PARSED, returns null.  Else, it tries to find a TheoremNode in
     * module moduleName "at" the point textSelection.  More precisely, it is the TheoremNode whose location
     * is the first one on the line containing the offset of textSelection.  
     * 
     * The method assumes that document is the document for the module.
     * 
     * @param parseResult
     * @param moduleName
     * @param textSelection
     * @param document
     * @return
     */
    public static TheoremNode getTheoremNodeWithCaret(ParseResult parseResult, String moduleName,
            ITextSelection textSelection, IDocument document)
    {
        if ((parseResult == null) || (parseResult.getStatus() != IParseConstants.PARSED))
        {
            return null;
        }
        ModuleNode module = parseResult.getSpecObj().getExternalModuleTable().getModuleNode(
                UniqueString.uniqueStringOf(moduleName));
        if (module == null)
        {
            return null;
        }
        TheoremNode[] theorems = module.getTheorems();

        TheoremNode stepWithCaret = null;

        for (int i = 0; i < theorems.length; i++)
        {
            TheoremNode theoremNode = theorems[i];

            if (theoremNode.getLocation().source().equals(moduleName))
            {
                /*
                 * Found a theorem in the module.
                 * 
                 * See if it has a step containing the caret.
                 * 
                 * The caret is located at the end of the current
                 * selection if a range of text is selected (highlighted).
                 */
                TheoremNode step = UIHelper.getThmNodeStepWithCaret(theoremNode, textSelection.getOffset()
                /* + textSelection.getLength() */, document);

                if (step != null)
                {
                    // found the step with the caret
                    stepWithCaret = step;
                    break;
                }
            }
        }

        return stepWithCaret;

    }

    /**
     * If parseResult's status is not equal to PARSED, returns null.  Else, it tries to find a {@link LevelNode}
     * representing a proof step or a top level USE/HIDE node in module moduleName "at" the point textSelection. 
     * More precisely, the caret is at a LevelNode if the level node is the innermost proof step or USE/HIDE node
     * whose step or proof contains the line with the caret and that is first on the line containing the caret. That
     * is, if there is more than one proof and/or step on the line with the caret, this method returns the first on
     * the line.
     * 
     * The method assumes that document is the document for the module.
     * 
     * Returns null if no step is found.
     * 
     * @param parseResult
     * @param moduleName
     * @param textSelection
     * @param document
     * @return
     */
    public static LevelNode getPfStepOrUseHideFromMod(ParseResult parseResult, String moduleName,
            ITextSelection textSelection, IDocument document)
    {
        try
        {

            if ((parseResult == null) || (parseResult.getStatus() != IParseConstants.PARSED))
            {
                return null;
            }
            ModuleNode module = parseResult.getSpecObj().getExternalModuleTable().getModuleNode(
                    UniqueString.uniqueStringOf(moduleName));

            return getPfStepOrUseHideFromModuleNode(module, document.getLineOfOffset(textSelection.getOffset()) + 1);
            // if (module == null)
            // {
            // return null;
            // }
            //
            // LevelNode[] topLevelNodes = module.getTopLevel();
            //
            // for (int i = 0; i < topLevelNodes.length; i++)
            // {
            //
            // if (topLevelNodes[i].getLocation().source().equals(moduleName))
            // {
            // /*
            // * If the level node is a use or hide node search to see if the
            // * caret is at that node. If the node is a theorem node, see if
            // * the caret is at a node in the tree rooted at the theorem node.
            // */
            // LevelNode node = getLevelNodeFromTree(topLevelNodes[i], document.getLineOfOffset(textSelection
            // .getOffset()) + 1);
            // if (node != null)
            // {
            // return node;
            // }
            // }
            //
            // }
        } catch (BadLocationException e)
        {
            Activator.getDefault().logError("Error getting line number of caret.", e);
        }
        return null;

    }

    /**
     * It tries to find a {@link LevelNode} representing a proof step or a top level
     * USE/HIDE node in module "at" the lineNum. More precisely, the lineNum is at a
     * LevelNode if the level node is the innermost proof step or USE/HIDE node
     * whose step or proof contains the lineNum and that is first on lineNum. That
     * is, if there is more than one proof and/or step on lineNum, this method returns the first on
     * the line.
     * 
     * Returns null if module is null or if no step is found.
     * 
     * @param module
     * @param lineNum
     * @return
     */
    public static LevelNode getPfStepOrUseHideFromModuleNode(ModuleNode module, int lineNum)
    {
        if (module == null)
        {
            return null;
        }

        LevelNode[] topLevelNodes = module.getTopLevel();

        for (int i = 0; i < topLevelNodes.length; i++)
        {

            /*
             * Top level nodes can be ones imported from extended modules.
             * We only want to look at those in the module.
             */
            if (topLevelNodes[i].getLocation().source().equals(module.getName().toString()))
            {
                /*
                 * If the level node is a use or hide node search to see if the
                 * caret is at that node. If the node is a theorem node, see if
                 * the caret is at a node in the tree rooted at the theorem node.
                 */
                LevelNode node = getLevelNodeFromTree(topLevelNodes[i], lineNum);
                if (node != null)
                {
                    return node;
                }
            }

        }
        return null;
    }

    /**
     * Returns the {@link LevelNode} in the tree rooted at levelNode that is the innermost
     * step such that lineNum is between the begin line of the step and the end line of the proof
     * if there is a proof or the begin and end lines of the step if there is no proof.
     * If there is more than one step or proof on lineNum, then this method returns the step
     * that is first on lineNum (or whose proof is first on lineNum).
     * Returns null if no such node found. Assumes that levelNode is one of
     * 
     * {@link UseOrHideNode}
     * {@link InstanceNode}
     * {@link TheoremNode}
     * {@link DefStepNode}
     * 
     * If that is not true, this method returns null.
     * 
     * In this example:
     * 
     * line 10: <2>1. X
     * line 11: \* The following proof is simple
     * line 12:    <3>1. Y
     * line 13:       OBVIOUS <3>2. Z
     * 
     * if lineNum = 10, this method returns <2>1. If lineNum = 11, this method again returns <2>1.
     * If lineNum = 12, this method returns <3>1. If lineNum = 13, this method again returns <3>1.
     * 
     * @param levelNode
     * @param lineNum
     * @return
     */
    public static LevelNode getLevelNodeFromTree(LevelNode levelNode, int lineNum)
    {
        /*
         * Get the location of the step.    
         * 
         * For a TheoremNode, the step is from the beginning of the theorem
         * node to the end of the statement of the
         * theorem node. TheoremNode.getTheorem() returns the node
         * corresponding to the statement of the step (or theorem).
         * 
         * For other nodes the location is simply the begin line
         * to the end line of the node.
         * 
         * Return levelNode if the caret is on any of the lines
         * from of the location of the node.
         * 
         * If the caret is not on any of those lines and the node is a TheoremNode, then
         * recursively search for a substep containing the caret. Since the steps
         * are recursively searched in order, this will return the step
         * that is first on lineNum, if there is such a step.
         */
        int nodeBeginLine = levelNode.getLocation().beginLine();
        int nodeEndLine = 0;
        if (levelNode instanceof TheoremNode)
        {
            nodeEndLine = ((TheoremNode) levelNode).getTheorem().getLocation().endLine();
        } else if (levelNode instanceof UseOrHideNode || levelNode instanceof InstanceNode
                     || levelNode instanceof DefStepNode)
        	/*
        	 * Comment added by LL on 4 Feb 2014:  To make the Prove command prove
        	 * the innermost enclosing proof when the cursor is on a HIDE or DEFINE step,
        	 * change the else if condition to (approximately)
        	 * 
        	 *       ((levelNode instanceof UseOrHideNode) && (((UseOrHideNode) levelNode).getKind() == ASTConstants.UseKind))
        	 *       
        	 *  Since we decided not to do this, I didn't check if this is correct.
        	 */
        {
            nodeEndLine = levelNode.getLocation().endLine();
        } else
        {
            return null;
        }

        if (nodeBeginLine <= lineNum && nodeEndLine >= lineNum)
        {
            return levelNode;
        }

        if (levelNode instanceof TheoremNode)
        {
            /*
             * If the theorem has a proof and the lineNum is between
             * the end of the statement and the end of the proof,
             * then if it is a non-leaf proof, recursively search for 
             * a substep. If none of these substeps are returned for containing
             * lineNum, return levelNode.  Otherwise, it is a leaf proof containing
             * the lineNum and we return levelNode.
             */
            TheoremNode theoremNode = (TheoremNode) levelNode;

            ProofNode proof = theoremNode.getProof();
            if (proof != null)
            {
                Location proofLoc = proof.getLocation();
                if (lineNum >= nodeEndLine && lineNum <= proofLoc.endLine())
                {
                    if (proof instanceof NonLeafProofNode)
                    {
                        NonLeafProofNode nonLeafProof = (NonLeafProofNode) proof;
                        LevelNode[] steps = nonLeafProof.getSteps();

                        for (int i = 0; i < steps.length; i++)
                        {
                            LevelNode node = getLevelNodeFromTree(steps[i], lineNum);
                            if (node != null)
                            {
                                return node;
                            }

                        }

                        /*
                         * If we reach this point, none of the steps of the proof contain
                         * the line number, but the proof of levelNode contains the line number.
                         * This means that levelNode is the innermost step whose step or proof
                         * contains line number, so we return levelNode.
                         */
                        return levelNode;
                    }

                    else
                    {
                        return levelNode;
                    }
                }
            }

        }
        return null;
    }

    /**
     * Returns a document representing the document given
     * by module name in the current spec (name without tla extension).
     * Note that this document will not be synchronized with changes to
     * the file. It will simply be a snapshot of the file.
     * 
     * @param moduleName
     * @return
     */
    public static IDocument getDocFromName(String moduleName)
    {
        IFile module = (IFile) getResourceByModuleName(moduleName);
        return getDocFromFile(module);
    }

    /**
     * Returns a document representing the file. Note that
     * this document will not be synchronized with changes to
     * the file. It will simply be a snapshot of the file.
     * 
     * Returns null if unsuccessful.
     * 
     * @param module
     * @return
     */
    public static IDocument getDocFromFile(IFile file)
    {

        /*
         * We need a file document provider to create
         * the document. After the document is created
         * the file document provider must be disconnected
         * to avoid a memory leak.
         */
        FileDocumentProvider fdp = new FileDocumentProvider();
        FileEditorInput input = new FileEditorInput(file);
        try
        {
            fdp.connect(input);
            return fdp.getDocument(input);
        } catch (CoreException e)
        {
            Activator.getDefault().logError("Error getting document for module " + file, e);
        } finally
        {
            fdp.disconnect(input);
        }
        return null;

    }

    /**
     * Called to find the number of bytes contained within an IResource
     * that represents a Java File object (a file or directory).  Returns
     * 0 if resource or its File are null.
     * 
     * @param resource
     * @return
     */
    public static long getSizeOfJavaFileResource(final IResource resource)
    {
        // Set file to the Java File represented by the resource.
        if (resource == null)
        {
            return 0;
        }
        // Check for resource.getLocation() = null added 30 May 2010
        // by LL.
        IPath ipath = resource.getLocation();
        if (ipath == null)
        {
            return 0;
        }
        File file = ipath.toFile();

        if (file == null)
        {
            return 0;
        }
        return getDirSize(file);
    }

    /**
     * If dir is a directory, return the size in bytes of all
     * @param dir
     * @return the size in bytes
     */
    private static long getDirSize(File dir)
    {
        long size = 0;
        if (dir.isFile())
        {
            size = dir.length();
        } else
        {
            File[] subFiles = dir.listFiles();
            // The following null pointer test added by LL on 25 Sep 2010.
            // I have no idea what's causing it to be null, but there seems
            // to be no point having it throw the exception, which might
            // conceivably be causing problems.
            if (subFiles == null)
            {
                return 0;
            }
            size += dir.length();
            for (int i = 0; i < subFiles.length; i++)
            {
                File file = subFiles[i];

                if (file.isFile())
                {
                    size += file.length();
                } else
                {
                    size += getDirSize(file);
                }
            }
        }
        return size;
    }

    /**
     * Returns true if the node is not from a standard module.
     * 
     * @param node
     * @return
     */
    public static boolean isFromUserModule(SemanticNode node)
    {
        SyntaxTreeNode csNode = (SyntaxTreeNode) node.stn;
        String name = ResourceHelper.getModuleFileName(csNode.getFilename());
        return ToolboxHandle.isUserModule(name);
    }

    /**
     * Return all the <code>OpApplNode</code>s in <code>module</code> whose
     * operator node equals <code>symbol</code>.
     * 
     * Modified by LL on 23 Dec 2012 to generalize the `module' parameter from a ModuleNode
     * to a SemanticNode for use in DecomposeProofHandler.  (This required no change to the
     * code except the change of argument type.)
     * 
     * @param symbol
     * @param module
     * @return
     */
    public static SemanticNode[] getUsesOfSymbol(SymbolNode symbol, SemanticNode module)
    {
        Vector<SemanticNode> found = new Vector<SemanticNode>(20); 
        innerGetUsesOfSymbol(symbol, module, found);
        SemanticNode[] value = new SemanticNode[found.size()];
        for (int i = 0; i < value.length; i++)
        {
            value[i] = (SemanticNode) found.elementAt(i);
        }
        return value;
    }

    /** 
     * Returns true iff either node = symbol or node is an OpDefNode or ThmOrAssumpDefNode whose
     * source equals symbol. 
     * @param node
     * @param symbol
     * @return
     */
    private static boolean sourceEquals(SemanticNode node, SymbolNode symbol)
    {
        if (node == symbol)
        {
            return true;
        }
        if (((node instanceof OpDefNode) && ((OpDefNode) node).getSource() == symbol))
        {
            return true;
        }
        if ((node instanceof ThmOrAssumpDefNode) && ((ThmOrAssumpDefNode) node).getSource() == symbol)
        {
            return true;
        }
        return false;
    }

    /**
     * The inner recursive method used by get UsesOfSymbol.  It appends all the appropriate
     * OpApplNodes  to <code>found</code>.
     * 
     * Note: modified by LL on 14 Sep 2010 so a subexpression name like 
     * Foo!1!(a) will be returned as a use of Foo.  This introduces another
     * case to be handled when trying to extract the symbol's occurrence from the 
     * OpApplNode containing the symbol.  This is the one case in which the symbol
     * is not really the operator of the OpApplNode.
     * 
     * @param symbol
     * @param node
     * @param found
     * @return
     */
    private static void innerGetUsesOfSymbol(SymbolNode symbol, SemanticNode node, Vector<SemanticNode> found)
    {
        SymbolNode[] defs = null;

        // We have to detect the following instances in which we get a use directly from
        // this node. There are three basic cases:
        // 1. This is an OpApplNode and the operator is a use. There are three subcases:
        //    (a) The operator equals symbol
        //    (b) The operator is an OpDefNode that represents a subexpression of the
        //        definition of symbol.
        //    (c) The operator is either an OpDefNode or a ThmOrAssumpDefNode whose
        //        source (in another module) is symbol.
        // 2. This is an OpArgNode whose operator either
        //    (a) equals symbol, or
        //    (b) is an OpDefNode whose source (in another module) is symbol
        // 3. This is a LeafProofNode or UseOrHideNode and one of the DEF entries either
        //    (a) equals symbol, or
        //    (b) is an OpDefNode or a ThmOrAssumpDefNode whose source (in another module) 
        //        is symbol
        if (node instanceof OpApplNode)
        { // check for case 1
            OpApplNode oan = (OpApplNode) node;
            if (sourceEquals(oan.getOperator(), symbol)
                    || ((oan.subExpressionOf != null) && sourceEquals(oan.subExpressionOf, symbol)))
            {
                found.add(node);
            }
        } else if ((node instanceof OpArgNode) && sourceEquals(((OpArgNode) node).getOp(), symbol))
        { // Case 2
            found.add(node);
        } else
        { // Check for case 3
            if (node instanceof LeafProofNode)
            {
                defs = ((LeafProofNode) node).getDefs();
            } else if (node instanceof UseOrHideNode)
            {
                defs = ((UseOrHideNode) node).defs;
            }

            // If defs is non-null, there is a defs clause to be checked.
            // Modified by LL on 11 Feb 2012 to add the defs.length != 0
            // clause, since the LeafProofNode.getDefs method returns a 
            // zero-length array.
            if (defs != null && defs.length != 0)
            {
                // Set stn to the syntax tree of the actual BY, USE or HIDE.
                // I believe that's equal to node.sty except for a USE or HIDE
                // HIDE that's a proof step, in which case it seems to be
                // stn.getHeirs()[1]. Set defIdx to the index of the "DEF" in the
                // node's syntax tree.
                UniqueString defStr = UniqueString.uniqueStringOf("DEF");
                int defIdx = -1;
                SyntaxTreeNode stn = ((SyntaxTreeNode) node.stn);
                if (stn.getKind() == SyntaxTreeConstants.N_ProofStep)
                {
                    if (stn.getHeirs().length > 1)
                    {
                        stn = stn.getHeirs()[1];
                    } else
                    {
                        Activator.getDefault().logWarning("Bug in ResourceHelper line 1435");
                    }
                }
                for (int i = 0; i < stn.getHeirs().length; i++)
                {
                    SyntaxTreeNode nd = stn.getHeirs()[i];
                    if (nd.image == defStr)
                    {
                        defIdx = i;
                        break;
                    }
                }
                // There should be a "DEF" token if defs != null, but
                // it doesn't hurt to check.
                if (defIdx != -1)
                {
                    // For every instance of the symbol that we find,
                    // we add to found a dummy SemanticNode whose location
                    // is the location field of the corresponding syntax-tree
                    // node.
                    for (int i = 0; i < defs.length; i++)
                    {
                        if (sourceEquals(defs[i], symbol))
                        {
                            // Because of the commas separating items, the i-th DEF
                            // item (in Java counting) should be 2*i + 1 position to
                            // the right of the "DEF"
                            if (defIdx + 2 * i + 1 < stn.getHeirs().length)
                            {
                                // NewSymbNode is the simplest SemanticNode that has a public
                                // constructor, so we use one as our dummy SemanticNode.
                                found.add(new NewSymbNode(null, null, stn.getHeirs()[defIdx + 2 * i + 1]));
                            } else
                            {
                                // If we get here, it means that there's no syntax
                                // tree node corresponding to defs[i].
                                Activator.getDefault().logWarning("Bug at ResourceHelper line 1471");
                            }
                        }
                    }
                } else
                {
                	Activator.getDefault().logWarning("Bug at ResourceHelper line 1477");
                }
            }
        }

        SemanticNode[] children = node.getChildren();
        if (children == null)
        {
            return;
        }
        for (int i = 0; i < children.length; i++)
        {
        	// The following null pointer test added by LL on 4 Dec 2011 to fix
        	// bug 233, which occurs because the OTHER clause in a CASE statement
        	// is indicated by the presence of a null instead of a test expression.
        	final SemanticNode sn = children[i];
        	if (sn != null) 
        	{
               if (node.getLocation().source().equals(sn.getLocation().source()))
               {
                innerGetUsesOfSymbol(symbol, sn, found);
               }
        	}
        }
        return;
    }
    
    /**
     * Return all the <code>OpApplNode</code>s and <code>OpArgNode</code>s in the 
     * expression or OpArgNode <code>expr</code> whose operator node is a 
     * user-defined operator.
     * 
     * @param symbol
     * @param expr
     * @return
     */
    public static ExprOrOpArgNode[] getUsesOfUserDefinedOps(SemanticNode expr)
    {
        Vector<ExprOrOpArgNode> found = new Vector<ExprOrOpArgNode>(20); 
        innerGetUsesOfUserDefinedOps(expr, found);
        ExprOrOpArgNode[] value = new ExprOrOpArgNode[found.size()];
        for (int i = 0; i < value.length; i++)
        {
            value[i] =  found.elementAt(i);
        }
        return value;
    }

    /** 
     * Returns true iff node is an OpApplNode or ExprOrOpArgNode whose operator 
     * is a user-defined operator.
     * 
     * @param node
     * @param symbol
     * @return
     */
    private static boolean hasUserDefinedOp(SemanticNode node)
    {
        if (! (node instanceof ExprOrOpArgNode)) {
            return false ;
        }
        
        SymbolNode sym ;
        
        if (node instanceof OpApplNode) {
            sym = ((OpApplNode) node).getOperator() ;
        } 
        else if (node instanceof OpArgNode) {
            sym = ((OpArgNode) node).getOp() ;
        }
        else {
            return false ;
        }
                      
        if (! (sym instanceof OpDefNode)) {
            return false ;
        }
        
        OpDefNode op = (OpDefNode) sym ;
        return op.getKind() == ASTConstants.UserDefinedOpKind ;
    }

    /**
     * The inner recursive method used by getUsesOfUserDefinedOps. It appends all the appropriate
     * OpApplNodes  to <code>found</code>.
     * 
     * @param node
     * @param found
     * @return
     */
    private static void innerGetUsesOfUserDefinedOps(SemanticNode node, Vector<ExprOrOpArgNode> found)
    {
        // We have to detect the following instances in which we get a use directly from
        // this node. There are three basic cases:
        // 1. This is an OpApplNode and the operator is a user-defined OpDef node. 
        // 2. This is an OpArgNode whose operator is a user-defined OpDef node.
        if (hasUserDefinedOp(node)) {
          found.add((ExprOrOpArgNode) node);

        } 
        SemanticNode[] children = node.getChildren();
        if (children == null)
        {
            return;
        }
        for (int i = 0; i < children.length; i++)
        {
            // The following null pointer test added by LL on 4 Dec 2011 to fix
            // bug 233, which occurs because the OTHER clause in a CASE statement
            // is indicated by the presence of a null instead of a test expression.
            final SemanticNode sn = children[i];
            if (sn != null) 
            {
               if (node.getLocation().source().equals(sn.getLocation().source()))
               {
                   innerGetUsesOfUserDefinedOps(sn, found);
               }
            }
        }
        return;
    }



    /**
     * Returns an array of all the user modules of the current 
     * specification.  Returns null if anything goes wrong, which
     * I don't think it should (but I don't know what will happen
     * if this is called with the spec unparsed).
     * 
     * @return
     */
    public static String[] getModuleNames()
    {
        // first we get the spec object.
        Spec spec = ToolboxHandle.getCurrentSpec();
        if (spec == null)
        {
            return null;
        }
        // then we get the full path name of the root module file
        String rootFileName = spec.getRootFilename();
        if (rootFileName == null)
        {
            return null;
        }

        // then we get the name of the root module
        String rootModuleName = getModuleNameChecked(rootFileName, false);
        if (rootModuleName == null)
        {
            return null;
        }

        // then we get the names of all user modules (with ".tla" appended)
        // imported (directly or indirectly) by the root file.
        ParserDependencyStorage pds = Activator.getModuleDependencyStorage();
        if (pds == null)
        {
            return null;
        }
        List<String> listOfImportedModules = pds.getListOfExtendedModules(rootModuleName + ".tla");

        // Then we put them in an array and sort them.
        String[] value = new String[listOfImportedModules.size() + 1];
        for (int i = 0; i < listOfImportedModules.size(); i++)
        {
            String element = listOfImportedModules.get(i);
            value[i] = element.substring(0, element.length() - 4);
        }
        value[listOfImportedModules.size()] = rootModuleName;
        Arrays.sort(value);
        return value;
    }

    /**
     * Returns a HashSet containing all user-definable names that are globally 
     * defined or declared at Location loc of the module.  The returned
     * value may or may not contain strings that are not user-definable names--in
     * particular strings like "I!bar".  
     * 
     * If the statement at loc defines or declares a symbol, that symbol does
     * not appear in the returned value.  However, the implementation assumes that
     * there there is no declaration or definition that begins on the same line
     * as the beginning of loc.  If there is, the symbol it defines will not 
     * appear in the returned result. 
     * 
     * The method also assumes that loc is after any EXTENDS statement in the
     * module.
     * 
     * @param module  The module.
     * @param loc     The location.
     * @return
     */
    public static HashSet<String> declaredSymbolsInScope(ModuleNode module, Location loc) {
        // result accumulates the return value.
        HashSet<String> result = new HashSet<String>() ;
        addDeclaredSymbolsInScope(result, module, loc);
        return result ;
    }
    
    /**
     * Like declaredSymbolsInScope, except instead of returning the computed value as a result,
     * it adds it to the elements of the `result' argument.
     * 
     * Note added by LL on 8 Oct 2014: This implementation seems silly.  It is pulling in symbols
     * defined or declared in all the modules EXTENDed by `module'.  However, all those symbols
     * should already be included in the defined and declared symbols of `module'.  However,
     * it appears that this doesn't cause the same string to be included multiple times
     * in the returned result.
     * 
     * @param result
     * @param module
     * @param loc
     */
    public static void addDeclaredSymbolsInScope(HashSet<String> result, ModuleNode module, Location loc) {
        // Set result to the set of all CONSTANT and VARIABLE declarations it should contain.
        // These are the ones from `module' that precede loc, and the ones from any extended
        // module.
        //
        // Testing on 9 Oct 2014 reveals that there is no need to look at EXTENDed modules
        // because those are already returned by the GetConstant/VariableDecls calls of
        // the module itself.
        HashSet<ModuleNode> extendees = module.getExtendedModuleSet(); 
        extendees.add(module) ;
        Iterator<ModuleNode> iter = extendees.iterator() ;
        while (iter.hasNext()) {
            ModuleNode modNode = iter.next() ;
            // Get CONSTANTS
            OpDeclNode[] decls = modNode.getConstantDecls() ;
            for (int i = 0; i < decls.length; i++) {
                if ((modNode != module) || earlierLine(decls[i].stn.getLocation(), loc)) {
                    result.add(decls[i].getName().toString()) ;
                }
            }
            
           // Get VARIABLES
            decls = modNode.getVariableDecls() ;
            for (int i = 0; i < decls.length; i++) {
                if ((modNode != module) || earlierLine(decls[i].stn.getLocation(), loc)) {
                    result.add(decls[i].getName().toString()) ;
                }
            }
        }
        
        // Set allModulesSet to the set of ModuleNodes containing module and all imported
        // modules that can contribute definitions or declarations of user-typeable symbols.
        // Add to `result' the set of all symbols sym that contribute to the final result from
        // statements of the form
        //
        //    sym == INSTANCE ...
        HashSet<ModuleNode> allModulesSet = new HashSet<ModuleNode>();
        addImportedModules(allModulesSet, result, loc, module) ;
        
        // Add defined operator and theorem names
        iter = allModulesSet.iterator();
        while (iter.hasNext()) {
            ModuleNode modNode = iter.next() ;
            
            // add definitions
            // On 8 Oct 2014, LL corrected a bug caused by the use of `module'
            // instead of `modNode' in the following statement.  This caused
            // all definitions and declarations from `module' to be returned
            // rather than just the ones appearing earlier in the module.
            OpDefNode[] decls = modNode.getOpDefs();
            for (int i = 0; i < decls.length; i++) {
                if ((modNode != module) || earlierLine(decls[i].stn.getLocation(), loc)) {
                    result.add(decls[i].getName().toString()) ;
                } 
            }
            
            // add theorems
            ThmOrAssumpDefNode[] tdecls = module.getThmOrAssDefs();
            for (int i = 0; i < tdecls.length; i++) {
                if ((modNode != module) || earlierLine(tdecls[i].stn.getLocation(), loc)) {
                    result.add(tdecls[i].getName().toString()) ;
                } 
            }
        };
    }
    
    /**
     * If node is an element of modules, it does nothing.  If it is then it
     * adds to <code>modules</code> all modules imported (directly or indirectly)
     * by module <code>node</code> by an EXTENDS statement or by an unnamed
     * INSTANCE occurring before Location <code>loc</code>.  It adds to 
     * <code>symbols</code> all symbols sym that occur in a
     * 
     *    sym == INSTANCE ...
     *    
     * statement that occurs in module <code>node</code> before location 
     * <code>loc</code> or anywhere in one of the modules added to <code>modules</code>.
     * 
     * This procedure is called by declaredSymbolsInScope and by itself, the
     * latter calls always with loc a Location beyond the end of any module.
     * 
     * @param modules
     * @param symbols
     * @param loc
     * @param node
     */
    public static void addImportedModules(HashSet<ModuleNode> modules, HashSet<String> symbols, 
                                   Location loc, ModuleNode node) {
        if (modules.contains(node)) {
            return ;
        }
        modules.add(node) ;
        
        HashSet<ModuleNode> extendees = node.getExtendedModuleSet();
        Iterator<ModuleNode> iter = extendees.iterator() ;
        while (iter.hasNext()) {
            ModuleNode modNode = iter.next() ;
            addImportedModules(modules, symbols, infiniteLoc, modNode) ;
        }
        
        InstanceNode[] instances = node.getInstances() ;
        for (int i = 0; i < instances.length; i++) {
            // We add the instance only if its comes before loc.
            // For a LOCAL instance, we add the module to `module' or its name to `symbols'
            // only if this is the initial call, which is the case iff  loc # infiniteLoc
            if ( earlierLine(instances[i].stn.getLocation(), loc)
                 && (   ! instances[i].getLocal()
                     || earlierLine(loc, infiniteLoc))){
               if (instances[i].getName() != null) {
                   symbols.add(instances[i].getName().toString()) ;
               } else {
                  // Testing on 9 Oct 2014 revealed that the following is unnecessary because
                  // the defined operators imported into a module M without renaming by an INSTANCE
                  // are contained in M.getOpDefs().  Imported named theorems are similarly
                  // contained in M.getThmOrAssDefs().
                  
                  addImportedModules(modules, symbols, infiniteLoc, instances[i].getModule()) ; 
               }
            }
        }     

    }

    /*
     * The following three methods are clones of the preceding three methods with HashSet<String>
     * arguments replaced by StringSet arguments.  These clones were made because where the 
     * original implementation of the Decompose Proof command used a HashSet<String> to hold a set
     * of operator names, while the new implementation uses a StringSet.
     */
    
    /**
     * Returns a HashSet containing all user-definable names that are globally 
     * defined or declared at Location loc of the module.  The returned
     * value may or may not contain strings that are not user-definable names--in
     * particular strings like "I!bar".  
     * 
     * If the statement at loc defines or declares a symbol, that symbol does
     * not appear in the returned value.  However, the implementation assumes that
     * there there is no declaration or definition that begins on the same line
     * as the beginning of loc.  If there is, the symbol it defines will not 
     * appear in the returned result. 
     * 
     * The method also assumes that loc is after any EXTENDS statement in the
     * module.
     * 
     * @param module  The module.
     * @param loc     The location.
     * @return
     */
    public static StringSet declaredSymbolsInScopeSet(ModuleNode module, Location loc) {
        // result accumulates the return value.
        StringSet result = new StringSet() ;
        addDeclaredSymbolsInScopeSet(result, module, loc);
        return result ;
    }
    
    /**
     * Like declaredSymbolsInScope, except instead of returning the computed value as a result,
     * it adds it to the elements of the `result' argument.
     * 
     * Note added by LL on 8 Oct 2014: This implementation seems silly.  It is pulling in symbols
     * defined or declared in all the modules EXTENDed by `module'.  However, all those symbols
     * should already be included in the defined and declared symbols of `module'.  However,
     * it appears that this doesn't cause the same string to be included multiple times
     * in the returned result.
     * 
     * @param result
     * @param module
     * @param loc
     */
    public static void addDeclaredSymbolsInScopeSet(StringSet result, ModuleNode module, Location loc) {
        // Set result to the set of all CONSTANT and VARIABLE declarations it should contain.
        // These are the ones from `module' that precede loc, and the ones from any extended
        // module.
        //
        // Testing on 9 Oct 2014 reveals that there is no need to look at EXTENDed modules
        // because those are already returned by the GetConstant/VariableDecls calls of
        // the module itself.
        HashSet<ModuleNode> extendees = module.getExtendedModuleSet(); 
        extendees.add(module) ;
        Iterator<ModuleNode> iter = extendees.iterator() ;
        while (iter.hasNext()) {
            ModuleNode modNode = iter.next() ;
            // Get CONSTANTS
            OpDeclNode[] decls = modNode.getConstantDecls() ;
            for (int i = 0; i < decls.length; i++) {
                if ((modNode != module) || earlierLine(decls[i].stn.getLocation(), loc)) {
                    result.add(decls[i].getName().toString()) ;
                }
            }
            
           // Get VARIABLES
            decls = modNode.getVariableDecls() ;
            for (int i = 0; i < decls.length; i++) {
                if ((modNode != module) || earlierLine(decls[i].stn.getLocation(), loc)) {
                    result.add(decls[i].getName().toString()) ;
                }
            }
        }
        
        // Set allModulesSet to the set of ModuleNodes containing module and all imported
        // modules that can contribute definitions or declarations of user-typeable symbols.
        // Add to `result' the set of all symbols sym that contribute to the final result from
        // statements of the form
        //
        //    sym == INSTANCE ...
        HashSet<ModuleNode> allModulesSet = new HashSet<ModuleNode>();
        addImportedModulesSet(allModulesSet, result, loc, module) ;
        
        // Add defined operator and theorem names
        iter = allModulesSet.iterator();
        while (iter.hasNext()) {
            ModuleNode modNode = iter.next() ;
            
            // add definitions
            // On 8 Oct 2014, LL corrected a bug caused by the use of `module'
            // instead of `modNode' in the following statement.  This caused
            // all definitions and declarations from `module' to be returned
            // rather than just the ones appearing earlier in the module.
            OpDefNode[] decls = modNode.getOpDefs();
            for (int i = 0; i < decls.length; i++) {
                if ((modNode != module) || earlierLine(decls[i].stn.getLocation(), loc)) {
                    result.add(decls[i].getName().toString()) ;
                } 
            }
            
            // add theorems
            ThmOrAssumpDefNode[] tdecls = module.getThmOrAssDefs();
            for (int i = 0; i < tdecls.length; i++) {
                if ((modNode != module) || earlierLine(tdecls[i].stn.getLocation(), loc)) {
                    result.add(tdecls[i].getName().toString()) ;
                } 
            }
        };
    }
    

    
    /**
     * If node is an element of modules, it does nothing.  If it is then it
     * adds to <code>modules</code> all modules imported (directly or indirectly)
     * by module <code>node</code> by an EXTENDS statement or by an unnamed
     * INSTANCE occurring before Location <code>loc</code>.  It adds to 
     * <code>symbols</code> all symbols sym that occur in a
     * 
     *    sym == INSTANCE ...
     *    
     * statement that occurs in module <code>node</code> before location 
     * <code>loc</code> or anywhere in one of the modules added to <code>modules</code>.
     * 
     * This procedure is called by declaredSymbolsInScope and by itself, the
     * latter calls always with loc a Location beyond the end of any module.
     * 
     * @param modules
     * @param symbols
     * @param loc
     * @param node
     */
    public static void addImportedModulesSet(HashSet<ModuleNode> modules, StringSet symbols, 
                                   Location loc, ModuleNode node) {
        if (modules.contains(node)) {
            return ;
        }
        modules.add(node) ;
        
        HashSet<ModuleNode> extendees = node.getExtendedModuleSet();
        Iterator<ModuleNode> iter = extendees.iterator() ;
        while (iter.hasNext()) {
            ModuleNode modNode = iter.next() ;
            addImportedModulesSet(modules, symbols, infiniteLoc, modNode) ;
        }
        
        InstanceNode[] instances = node.getInstances() ;
        for (int i = 0; i < instances.length; i++) {
            // We add the instance only if its comes before loc.
            // For a LOCAL instance, we add the module to `module' or its name to `symbols'
            // only if this is the initial call, which is the case iff  loc # infiniteLoc
            if ( earlierLine(instances[i].stn.getLocation(), loc)
                 && (   ! instances[i].getLocal()
                     || earlierLine(loc, infiniteLoc))){
               if (instances[i].getName() != null) {
                   symbols.add(instances[i].getName().toString()) ;
               } else {
                  // Testing on 9 Oct 2014 revealed that the following is unnecessary because
                  // the defined operators imported into a module M without renaming by an INSTANCE
                  // are contained in M.getOpDefs().  Imported named theorems are similarly
                  // contained in M.getThmOrAssDefs().
                  
                  addImportedModulesSet(modules, symbols, infiniteLoc, instances[i].getModule()) ; 
               }
            }
        }     

    }
    
    /**
     * A location beyond the end of any module.
     */
    public static final Location infiniteLoc = 
          new Location(Integer.MAX_VALUE, 0, Integer.MAX_VALUE, Integer.MAX_VALUE) ;
    
    /**
     * True iff the beginning line of loc1 is less than the beginning line of loc2.
     * 
     * @param loc1
     * @param loc2
     * @return
     */
    private static boolean earlierLine(Location loc1, Location loc2) {
        return loc1.beginLine() < loc2.beginLine() ;
    }
    
    
    /**
     * This Runnable class is used to raise an error message from a non-UI
     * thread.  (If running MessageDialog.openError throws a null-pointer
     * exception, this is the mechanism you should use instead.)  To
     * raise an error-message dialog, execute
     * 
     *   UIHelper.runUIAsync(
     *     new ResourceHelper.ErrorMessageRunnable(title, message)) ;
     *     
     * where `title' and `message' are the title and error message of the
     * dialog.
     * 
     * This method of raising the dialog was provided by Dan Ricketts.
     * 
     * @author lamport
     *
     */
    public static class ErrorMessageRunnable implements Runnable {
        String title ;
        String message ;
        
        public ErrorMessageRunnable(String tit, String msg) {
          this.title = tit ;
          this.message = msg ;
        }
        public void run() {
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    title, message);
        }
    }
    
    /**
     * Returns the FormalParmNode for all bound identifiers that are declared
     * in expr.  These are the bound identifiers introduced OpApplNodes.  They do
     * not include ones introduced as definition parameters in a LET definition.
     * 
     * This method was introduced for bound identifier renaming in the DecomposeProofHandler
     * methods.  For that, it would be nice to also return the symbols introduced by LET
     * definitions--both the defined operators and the definition parameters.  However,
     * it complicates things to handle the defined operators, since there's no FormalParamNode
     * corresponding to them.  And if we're not doing that, then there seems to be little point
     * worrying about their definition parameters. 
     * 
     * @param expr
     * @return
     */
    public static FormalParamNode[] getBoundIdentifiers(ExprNode expr) {
        Vector<FormalParamNode> vec = new Vector<FormalParamNode>() ; 
        innerGetBoundIdentifiers(vec, expr) ;
        FormalParamNode[] result = new FormalParamNode[vec.size()] ;
        for (int i=0; i < result.length; i++) {
            result[i] = vec.elementAt(i) ;
        }
        return result;
    }
    
    /**
     * This is the recursive operator that implements getBoundIdentifiers.  It adds the
     * bound identifiers in expr to those in vec.  The identifiers in vec should be different
     * from the ones declared in expr.
     * 
     * @param vec
     * @param expr
     */
    private static void innerGetBoundIdentifiers(Vector<FormalParamNode> vec,
            ExprNode expr) {
        if (expr instanceof OpApplNode) {
            OpApplNode node = (OpApplNode) expr;
            if (node.getUnbdedQuantSymbols() != null) {
                for (int i = 0; i < node.getUnbdedQuantSymbols().length; i++) {
                    vec.add(node.getUnbdedQuantSymbols()[i]);
                }
            }

            if (node.getBdedQuantSymbolLists() != null) {
                for (int i = 0; i < node.getBdedQuantSymbolLists().length; i++) {
                    FormalParamNode[] nodeList = node.getBdedQuantSymbolLists()[i];
                    for (int j = 0; j < nodeList.length; j++) {
                        vec.add(nodeList[j]);
                    }
                    innerGetBoundIdentifiers(vec, node.getBdedQuantBounds()[i]);
                }
            }

            for (int i = 0; i < node.getArgs().length; i++) {
                if (node.getArgs()[i] instanceof ExprNode) {
                    innerGetBoundIdentifiers(vec, (ExprNode) node.getArgs()[i]);
                }
            }
        } else if (expr instanceof LetInNode) {
            // We'd like to add the names declared in the LET/IN, but
            // they're not FormalParamNodes.  Instead, we add the 
            // LET declaration parameters and recursively call the method
            // on the IN clause (the body).
            LetInNode node = (LetInNode) expr ;
            for (int i=0; i < node.getLets().length; i++) {
                OpDefNode def = node.getLets()[i] ;
                for (int j = 0; j < def.getParams().length; j++) {
                    vec.add(def.getParams()[j]) ;
                }
                innerGetBoundIdentifiers(vec, node.getBody()) ;
                return ;
            }
        } else {
            return ;
        }
    }
    
    /**
     * Checks a specification name for its validity WRT the parser identifier definition
     * @param aSpecName The intended specification name to check for validity
     * @return true if the given spec name is a valid identifier
     */
	public static boolean isValidSpecName(final String aSpecName) {
		String identifier = getIdentifier(aSpecName);
		// verify given spec name and parsed spec name are the same
		return aSpecName.equals(identifier);
	}
	

	public static String getIdentifier(String aSpecName) {
		// in memory stream of spec name
		final ByteArrayInputStream stream = new ByteArrayInputStream(
				aSpecName.getBytes());
		
		// create a parser that operates on the spec name
		TLAplusParser tlaParser = new TLAplusParser(stream);

		// switch parser into spec mode
		tlaParser.token_source.SwitchTo(TLAplusParserConstants.SPEC);

		// try to consume an identifier
		try {
			return tlaParser.Identifier().getImage();
		} catch (ParseException e) {
			// not expected to happen but handle anyway
			return "";
		}
	}

	public static boolean isValidLibraryLocation(final String location) {
		if (location != null && location.length() > 0) {
			IPath path = new Path(location);		
			File directory = path.toFile();
			return directory.exists() && directory.isDirectory();
		}
		return false;
	}


	/**
	 * @param project
	 *            The project the mapping belongs to
	 * @param filename
	 *            The filename the mapping is for (without the mapping suffix
	 *            {@link ResourceHelper#PMAP_SUFFIX})
	 * @return A {@link TLAtoPCalMapping} or <code>null</code> if no mapping
	 *         exist or de-serialization on the mapping on disk fails.
	 */
	public static TLAtoPCalMapping readTLAtoPCalMapping(final IProject project, final String filename) {
		final IFile file = project.getFile(filename + PMAP_SUFFIX);
		if (file.exists()) {
			try {
				final ObjectInputStream inputStream = new ObjectInputStream(
						new FileInputStream(file.getLocation().toOSString()));
				final Object object = inputStream.readObject();
				inputStream.close();
				if (object instanceof TLAtoPCalMapping) {
					return (TLAtoPCalMapping) object;
				}
			} catch (final InvalidClassException e) {
				final String error = "The TLA+ to PCal mapping file "
						+ filename +
						".pmap has likely been generated with an older version of the TLA+ Toolbox. " +
						"Please (re)move the old file out of the way and retranslate your PCal algorithm again.\n" +
						"If you do not retranslate TLA+ to PCal mapping will not work.\n" +
						"(If moving the file does not fix this error, then please report a bug).";
				Activator.getDefault().logInfo(error);
				Activator.getDefault().logDebug(error, e);
			} catch (final FileNotFoundException e) {
				e.printStackTrace();
			} catch (final IOException e) {
				e.printStackTrace();
			} catch (final ClassNotFoundException e) {
				e.printStackTrace();
			}
		}
		return null;
	}

	/**
	 * @param project The project the mapping belongs to 
	 * @param filename The filename the mapping is for
	 * @param mapping The mapping to be written
	 * @param monitor  A status monitor that indicates progress
	 * @return true iff mapping successfully written to disk
	 */
	public static boolean writeTLAtoPCalMapping(final IProject project,
			final String filename, final TLAtoPCalMapping mapping, final IProgressMonitor monitor) {
		final IFile file = project.getFile(filename + PMAP_SUFFIX);
		try {
			final ObjectOutputStream outputStream = new ObjectOutputStream(
					new FileOutputStream(file.getLocation().toOSString()));
			outputStream.writeObject(mapping);
			outputStream.close();
			monitor.worked(1);
		} catch (final FileNotFoundException e) {
			e.printStackTrace();
			return false;
		} catch (final IOException e) {
			e.printStackTrace();
			return false;
		}
		return true;
	}

	/**
	 * Projects can have linked files (resources more generally). Linked resources a listed in the
	 * project's .project metadata.
	 * 
	 * @param project The project of which the given file (name) is assumed to be a linked file
	 * @param name The name of the link
	 * @return true iff the given name is indeed a *linked* file of the given project.
	 */
	public static boolean isLinkedFile(IProject project, String name) throws CoreException {
        final IFile file = project.getFile(new Path(new Path(name).lastSegment()));
        return file.isLinked(IResource.CHECK_ANCESTORS);
	}

	/**
	 * This does *not* work when the path are both pointing to an identical file
	 * but either is a symlink. This shouldn`t matter much for the Toolbox
	 * though (hope so).
	 * <p>
	 * A scenario where the previous claim is plain wrong is when running
	 * SpecTest on Mac OS X. Both /var/ and /tmp are symlinks pointing into
	 * /private/... and SpecTest thus fails because isProjectParent returns
	 * false. project.getLocation returns the resolved path /private/var/...
	 * whereas aFileName is /var/...
	 * @see SpecTest and AddModuleHandlerTest
	 * 
	 * @param aFileName
	 * @param project
	 * @return true iff aPath points to the parent folder of the given project
	 */
	public static boolean isProjectParent(final IPath aFileName, final IProject project) {
		return aFileName.equals(project.getLocation().removeLastSegments(1));
	}

	public static final String PARENT_ONE_PROJECT_LOC = "PARENT-1-PROJECT_LOC/";
}
