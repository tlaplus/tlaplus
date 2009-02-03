package org.lamport.tla.toolbox.util;

import java.io.File;

import org.eclipse.core.resources.ICommand;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IProjectDescription;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.Path;
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
                if (getParentDir(rootFilename) != null)
                {
                    // parent directory could be determined
                    IPath path = new Path(getParentDir(rootFilename)).removeTrailingSeparator();
                    path = path.append(name.concat(".toolbox")).addTrailingSeparator();
                    description.setLocation(path);
                }

                // set TLA+ feature
                description.setNatureIds(new String[] { TLANature.ID });

                // set Parsing Builder
                ICommand command = description.newCommand();
                command.setBuilderName(TLAParsingBuilder.BUILDER_ID);
                description.setBuildSpec(new ICommand[] { command });

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
     * @param createNew, a boolean flag indicating if the file should be created if it does not exist
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
    public static String getParentDir(String path)
    {
        File f = new File(path);
        if (f != null)
        {
            return f.getParent();
        }
        return null;
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
        //String modulename = f.getName().substring(0, f.getName().lastIndexOf("."));
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
     * TODO move somewhere else 
     * @param moduleFileName, name of the file 
     * @return the stream with content
     */
    public static byte[] getModuleDefaultContent(String moduleFilename)
    {
        StringBuffer buffer = new StringBuffer();
        buffer.append("---- MODULE ").append(ResourceHelper.getModuleNameChecked(moduleFilename, false)).append(" ----\n").append(
                "\n\n").append("====\n");
        return buffer.toString().getBytes();
    }

}
