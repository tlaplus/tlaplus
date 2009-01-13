package org.lamport.tla.toolbox.util;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.net.URL;
import java.util.Enumeration;
import java.util.Vector;

import org.eclipse.core.runtime.FileLocator;
import org.lamport.tla.toolbox.Activator;

import tla2sany.modanalyzer.NamedInputStream;
import tla2sany.modanalyzer.StringToNamedInputStream;
import util.ToolIO;

/**
 * RCP version of the name resolver for localization of the TLA modules
 * 
 * @author zambrovski
 */
public class RCPNameToFileIStream implements StringToNamedInputStream
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
            Enumeration installedInternalModules = Activator.getDefault().getBundle().findEntries("/",
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
     * Tries to find the specified module. It starts in work directory and then looks up in to the library paths for
     * modules.
     * 
     * @see tla2sany.modanalyzer.StringToNamedInputStream#toIStream(java.lang.String)
     */
    public NamedInputStream toIStream(String name)
    {

        if (name.endsWith(".tla"))
        {
            name = name.substring(0, name.length() - 4);
        }

        String sourceFileName = name + ".tla"; // could be Foo.tla or user/Foo.tla
        String sourceModuleName = name.substring(name.lastIndexOf(File.separator) + 1); // Foo.tla
        File sourceFile = locate(sourceFileName);

        if (sourceFile != null && sourceFile.exists())
        {
            try
            {
                NamedInputStream nis = new NamedInputStream(sourceFileName, sourceModuleName, sourceFile);
                return nis;
            } catch (FileNotFoundException e)
            {
                // TODO improve this
                ToolIO.out.println("***Internal error: Unable to create NamedInputStream" + " in toIStream method");
            }
        }
        return null;
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
            // TODO improve this: ToolIO.getUserDir()
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
