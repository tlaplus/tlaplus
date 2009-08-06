package org.lamport.tla.toolbox.util;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.Enumeration;
import java.util.Vector;

import org.eclipse.core.runtime.FileLocator;
import org.lamport.tla.toolbox.Activator;

import util.FilenameToStream;
import util.ToolIO;

/**
 * RCP version of the name resolver for localization of the TLA modules
 * 
 * @author zambrovski
 */
public class RCPNameToFileIStream implements FilenameToStream
{

    // TODO move to generic contsant interface
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


}
