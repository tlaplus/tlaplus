package org.lamport.tla.toolbox.util;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.Enumeration;
import java.util.Vector;

import org.eclipse.core.runtime.FileLocator;
import org.lamport.tla.toolbox.Activator;

import tla2sany.semantic.ModuleNode;
import util.FilenameToStream;
import util.ToolIO;

/**
 * RCP version of the name resolver for locating the TLA modules
 *
 * @author zambrovski
 */
public class RCPNameToFileIStream implements FilenameToStream
{

    // TODO move to generic constant interface
    public static final String STANDARD_MODULES   = "StandardModules";
    private Vector             libraryPathEntries = new Vector();

    /**
     * Initialization of the name resolver <br>
     * <b>Note:</b> the last location searched is the build-in location with standard modules introduced in the book
     *
     * @param libraryPathEntries
     *            - directories where to look for modules, or null if no user locations should be searched
     */
    public RCPNameToFileIStream(String[] libraryPathEntries)
    {
        // user modules
        if (libraryPathEntries != null)
        {
            for (int i = 0; i < libraryPathEntries.length; i++)
            {
                if (new File(libraryPathEntries[i]).exists())
                {
                    this.libraryPathEntries.addElement(libraryPathEntries[i]);
                }
            }
        }
        // standard modules
        initInternalLibraryPath();
    }

    /**
     * Initialization of RCP internal location of standard modules
     */
    private void initInternalLibraryPath()
    {
        try
        {
            Enumeration installedInternalModules = Activator.getDefault().getBundle().findEntries(File.separator,
                    STANDARD_MODULES, true);
            Vector paths = new Vector();
            while (installedInternalModules.hasMoreElements())
            {
                URL library = (URL) installedInternalModules.nextElement();
                if (library != null)
                {
                    // add external (resolved) URL
                    paths.addElement(FileLocator.resolve(library).getPath());
                }
            }
            libraryPathEntries.addAll(paths);
        } catch (IOException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }

    }

    /**
     * Tries to find the specified module.
     * Starts in work directory and then looks up in to the library paths for modules.
     *
     * @see {@link util.FilenameResolver#resolve(java.lang.String, boolean)}
     */
    public File resolve(String name, boolean isModule)
    {
        if (isModule && name.endsWith(".tla"))
        {
            // user/Foo.tla => user/Foo
            name = name.substring(0, name.length() - 4);
        }

        String sourceFileName;
        if (isModule)
        {
            // user/Foo => user/Foo.tla
            sourceFileName = name + ".tla"; // could be Foo.tla or user/Foo.tla
        } else {
            // user/Foo.cfg => user/Foo.cfg
            sourceFileName = name;
        }

        File sourceFile = locate(sourceFileName);
        return sourceFile;
    }

    /**
     * Searches for the file in current directory (ToolIO.userDirectory) and in library paths
     *
     * @param name
     *            - name of the file to look for
     * @return a File handle. Even if the file does not exist, the handle is not null
     */
    private final File locate(String name)
    {
        String prefix = "";

        File sourceFile = null;
        int idx = 0;
        while (true)
        {
            // improve this: ToolIO.getUserDir()
            if ((idx == 0) && (ToolIO.getUserDir() != null))
            {
                sourceFile = new File(ToolIO.getUserDir(), name);
            } else
            {
                sourceFile = new File(prefix + name);
            }
            if (sourceFile.exists())
                break;
            if (idx >= libraryPathEntries.size())
                break;

            prefix = (String) libraryPathEntries.elementAt(idx++);
        }
        return sourceFile;

    }

	/**
	 * Returns true iff moduleName is the name of a standard module.
	 * Because we are in the Toolbox code, we can use ResourceHelper.isFromUserModule
	 * to compute the result.  This is useful because the code from SimpleFileNameToStream
	 * doesn't work because the libraryPathEntries entry for the StandardModules
	 * directory appears as a URL rather than a path name--which means it has "/"
	 * as a name separator so it can't easily be compared to the file path name, which
	 * on Windows has "\\" as a name separator.
	 *
	 * Added by LL on 24 July 2013.
	 */
	public boolean isStandardModule(String moduleName) {
		ModuleNode moduleNode = ResourceHelper.getModuleNode(moduleName) ;
		if (moduleNode == null) {
			return false ;
		}
		return ! ResourceHelper.isFromUserModule(moduleNode) ;

	}
  /**
   * August 2014 - TL
   * added a stub for this informative interface method.
   * All the usages of this class were written before the
   * addition of this interface method and therefore this
   * method is not being called up to this point in time.
   */
  public String getFullPath(){
    throw new UnsupportedOperationException("method getFullPath is not supported for this class");
  }
}
