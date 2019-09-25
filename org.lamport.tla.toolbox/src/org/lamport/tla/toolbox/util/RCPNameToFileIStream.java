package org.lamport.tla.toolbox.util;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.nio.file.FileSystem;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Set;
import java.util.Vector;
import java.util.stream.Collectors;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Platform;
import org.osgi.framework.Bundle;

import tla2sany.semantic.ModuleNode;
import tlc2.module.BuiltInModuleHelper;
import util.FilenameToStream;
import util.ToolIO;

/**
 * RCP version of the name resolver for locating the TLA modules
 *
 * @author zambrovski
 */
public class RCPNameToFileIStream implements FilenameToStream
{

    private final Vector<String> libraryPathEntries = new Vector<String>();

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
        	final Bundle bundle = Platform.getBundle(BuiltInModuleHelper.BUNDLE_ID);
        	
			Enumeration<URL> installedInternalModules = bundle
					.findEntries(BuiltInModuleHelper.STANDARD_MODULES_PATH, BuiltInModuleHelper.STANDARD_MODULES, true);
			
			if (installedInternalModules == null) {
				// Toolbox is running from inside Eclipse (dev mode) and the StandardModules are
				// found in a slightly different location.
				installedInternalModules = bundle.findEntries(
						File.separator + "src" + File.separator + BuiltInModuleHelper.STANDARD_MODULES_PATH,
						BuiltInModuleHelper.STANDARD_MODULES, true);
			}
			
            while (installedInternalModules.hasMoreElements())
            {
                final URL library = installedInternalModules.nextElement();
                if (library != null)
                {
                    // add external (resolved) URL
                	final String path = FileLocator.resolve(library).getPath();
                	libraryPathEntries.add(path);
                }
            }
        } catch (IOException e)
        {
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
                sourceFile = new TLAFile(ToolIO.getUserDir(), name);
            } else
            {
            	if(FilenameToStream.isArchive(prefix)) {
            		sourceFile = getFromArchive(prefix, name);
    				if(sourceFile != null) {
    					return sourceFile;
    				}
            	} else {
                    sourceFile = new TLAFile(prefix + name, true);
            	}
            }
            if (sourceFile != null && sourceFile.exists()) {
            	break;
            }
            if (idx >= libraryPathEntries.size()) {
            	break;
            }

            prefix = (String) libraryPathEntries.elementAt(idx++);
        }
        return sourceFile;

    }
    
	// Extract the archive to a temporary directory from where the Toolbox will read
	// the resource. The problem is, that the Toolbox and TLC work with File instead
	// of InputStream which is why we can't extract to memory only.
	private File getFromArchive(String prefix, String name) {
		final File outputFile = new TLAFile(TMPDIR + File.separator + name, true);
		outputFile.deleteOnExit(); // Written to TMPDIR which is likely deleted regularly anyway.
		try (FileSystem fileSystem = FileSystems.newFileSystem(new File(prefix).toPath(), null)) {
	        Path fileToExtract = fileSystem.getPath(name);
	        Files.copy(fileToExtract, outputFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
	        return outputFile;
	    } catch (IOException e) {
			return null;
		}
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

	@Override
	public boolean isLibraryModule(String moduleName) {
		return isStandardModule(moduleName);
	}
	
	/**
	 * August 2014 - TL added a stub for this informative interface method. All
	 * the usages of this class were written before the addition of this
	 * interface method and therefore this method is not being called up to this
	 * point in time.
	 */
	public String getFullPath() {
		StringBuffer buf = new StringBuffer();
		for (int i = 0; i < libraryPathEntries.size(); i++) {
			buf.append(libraryPathEntries.elementAt(i));
			if (i < libraryPathEntries.size() - 1) {
				buf.append(", ");
			}
		}
		return buf.toString();
	}
    
	/**
	 * @return The set of the names of all modules found in the various
	 * libraryPathEntries (Toolbox & TLC installation, spec directories, library
	 * directories, and library archives.
	 * <p>
	 * This are not the modules extended by the current spec.
	 */
    public Set<String> getAllModules() {
    	final Set<String> s = new HashSet<>();
    	for (final String path : libraryPathEntries) {
    		if(FilenameToStream.isArchive(path)) {
    			s.addAll(listTLAFilesInZip(path));
    		} else {
    			// List .tla files in the given directory.
				s.addAll(Arrays.stream(new File(path).listFiles((d, name) -> name.endsWith(".tla")))
						.map(f -> f.getName()).collect(Collectors.toSet()));
    		}
		}
    	return s;
    }
    
    private Set<String> listTLAFilesInZip(String path) {
    	final Set<String> s = new HashSet<>();
		try (final ZipFile zipFile = new ZipFile(path)) {
			final Enumeration<? extends ZipEntry> e = zipFile.entries();
			while (e.hasMoreElements()) {
				ZipEntry entry = e.nextElement();
				String entryName = entry.getName();
				if (entryName.endsWith(".tla")) {
					s.add(entryName);
				}
			}
		} catch (IOException ignored) {
		}
		return s;
    }
}
