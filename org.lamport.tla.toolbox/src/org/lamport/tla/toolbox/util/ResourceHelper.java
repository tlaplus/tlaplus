package org.lamport.tla.toolbox.util;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.util.Date;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceRuleFactory;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.MultiRule;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.job.NewTLAModuleCreationOperation;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.nature.PCalDetectingBuilder;
import org.lamport.tla.toolbox.spec.nature.TLANature;
import org.lamport.tla.toolbox.spec.nature.TLAParsingBuilder;

/**
 * A toolbox with resource related methods
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ResourceHelper
{

    /**
     * Look up if a project exist and return true if so
     * @param name name of the project
     * @return
     */
    public static boolean peekProject(String name, String rootFilename) 
    {
        String root = getParentDirName(rootFilename); 
        File projectDir = new File(root.concat("/").concat(name).concat(".toolbox"));
        return projectDir.exists();
    }
    /**
     * Retrieves a project by name or creates a new project
     * <br><b>Note:</b> If the project does not exist in workspace it will be created, based
     * on the specified name and the path of the rootFilename. <br>The location (directory) of 
     * the project will be constructed as 
     * the parent directory of the rootFile + specified name + ".toolbox". 
     * <br>Eg. calling <tt>getProject("for", "c:/bar/bar.tla")</tt>
     * will cause the creation of the project (iff this does not exist) with location
     * <tt>"c:/bar/foo.toolbox"</tt>
     * 
     * 
     * @param name
     *            name of the project, should not be null
     * @param rootFilename 
     *            path to the root filename, should not be null 
     * @return a working IProject instance
     */
    public static IProject getProject(String name, String rootFilename)
    {
        if (name == null)
        {
            return null;
        }
        IWorkspace ws = ResourcesPlugin.getWorkspace();
        IProject project = ws.getRoot().getProject(name);

        // create a project
        if (!project.exists())
        {
            try
            {
                if (rootFilename == null)
                {
                    return null;
                }

                // create a new description for the given name
                IProjectDescription description = ws.newProjectDescription(name);

                // set project location
                if (getParentDirName(rootFilename) != null)
                {
                    // parent directory could be determined
                    IPath path = new Path(getParentDirName(rootFilename)).removeTrailingSeparator();
                    path = path.append(name.concat(".toolbox")).addTrailingSeparator();
                    description.setLocation(path);
                }

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

                // create the project
                // TODO add progress monitor
                project.create(description, null);

                // open the project
                // TODO add progress monitor
                project.open(null);

            } catch (CoreException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }

        return project;

    }

    /**
     * Retrieves a a resource from the project, creates a link, if the file is not present 
     * TODO improve this, if the name is wrong
     * 
     * @param name full filename of the resource
     * @param project
     * @param createNew, a boolean flag indicating if the new link should be created if it does not exist
     */
    public static IFile getLinkedFile(IProject project, String name, boolean createNew)
    {
        if (name == null || project == null)
        {
            return null;
        }
        IPath location = new Path(name);
        IFile file = project.getFile(location.lastSegment());
        if (createNew && !file.isLinked())
        {
            try
            {
                // TODO add progress monitor
                file.createLink(location, IResource.NONE, null);
                return file;

            } catch (CoreException e)
            {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
        return file;
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
        File f = new File(path);
        if (f != null)
        {
            return f.getParent();
        }
        return null;
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
     * Retrieves the name of the module (filename without extension)
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
            return moduleName.concat(".tla");
        }
    }

    /**
     * Determines if the given member is a TLA+ module
     * @param resource
     * @return
     */
    public static boolean isModule(IResource resource)
    {
        return (resource != null && "tla".equals(resource.getFileExtension()));

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
        buffer.append("---- MODULE ").append(ResourceHelper.getModuleNameChecked(moduleFilename, false)).append(
                " ----\n").append("\n\n");
        return buffer;
    }

    /**
     * Returns the content for the end of the module
     * @return
     */
    public static StringBuffer getModuleClosingTag()
    {
        StringBuffer buffer = new StringBuffer();
        buffer.append("====\n").append("\\* Generated at ").append(new Date());
        return buffer;
    }

    /**
     * Returns the content for the end of the module
     * @return
     */
    public static StringBuffer getConfigClosingTag()
    {
        StringBuffer buffer = new StringBuffer();
        buffer.append("\\* Generated at ").append(new Date());
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
                " ----\n").append("EXTENDS ").append(extendedModuleName).append(", TLC").append("\n\n");
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
            // System.out.println(buffer.toString());
            file.setContents(stream, IResource.FORCE | IResource.KEEP_HISTORY, monitor);
        } else
        {
            throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Exected " + file.getName() + " file has been removed externally"));
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
            // System.out.println(buffer.toString());
            file.appendContents(stream, IResource.FORCE | IResource.KEEP_HISTORY, monitor);
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
     * Renames and moves the project
     * @param project
     * @param specName
     */
    public static IProject projectRename(IProject project, String specName)
    {
        IProgressMonitor monitor = null;
        try
        {
            IProjectDescription description = project.getDescription();
            
            // move the project location
            IPath path = description.getLocation().removeLastSegments(1).removeTrailingSeparator().append(specName.concat(".toolbox")).addTrailingSeparator();
            description.setLocation(path);
            description.setName(specName);
            
            project.copy(description, IResource.NONE | IResource.SHALLOW, monitor);
            project.delete(IResource.NONE, monitor);
            
            return ResourcesPlugin.getWorkspace().getRoot().getProject(specName);
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }
    /**
     * Deletes the project
     * @param project
     */
    public static void deleteProject(IProject project)
    {
        IProgressMonitor monitor = null;
        try
        {
            project.delete(true, monitor);
        } catch (CoreException e)
        {
            e.printStackTrace();
        }
    }

}
