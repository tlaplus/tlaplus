// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package util;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.regex.Pattern;


/**
 * Resolver for the name to file handle.
 *
 * LL comment: 24 July 2013: I believe that the only classes that implements this
 * are SimpleFileNameToStream, RCPNameToFileIStream, and RMIFilenameToStreamResolver.
 * I added the isStandardModule method.
 *
 * @author Leslie Lamport
 * @author Simon Zambrovski
 */
public interface FilenameToStream
{

	/*
	 * Higher layers of TLC (and the Toolbox) have to determine if a module was
	 * loaded from a library location s.a. those defined by TLA_LIBRARY (see
	 * SimpleFilenameToStream). Thus, capture this information at module load
	 * time when it is known where a module was loaded from.
	 */
	@SuppressWarnings("serial")
	public static class TLAFile extends File {
		// The following regex is concerned with determining whether the provided 'parent' string to our
		//	parent/child constructor looks like the start of a legal absolute file path potentially including
		//	a drive letter.
		private static final String ROOT_PATH_REGEX
								= "^([a-zA-Z]+:)?" + ((File.separatorChar == '\\') ? "\\\\" : File.separator);
		private static final Pattern ROOT_PATH_PATTERN = Pattern.compile(ROOT_PATH_REGEX);
		
		
		private final boolean isLibraryModule;
		private transient final FilenameToStream resolver;
		// may be null.
		private final URI libraryPath;

		public TLAFile(String pathname, FilenameToStream fts) {
			this(pathname, false, fts);
		}

		public TLAFile(String pathname, boolean isLibraryModule, FilenameToStream fts) {
			super(pathname);
			this.isLibraryModule = isLibraryModule;
			this.libraryPath = this.exists() ? this.toURI() : null;
			this.resolver = fts;
		}

		public TLAFile(Path path, boolean isLibraryModule, FilenameToStream fts) {
			this(path.toFile().toString(), isLibraryModule, fts);
		}

		public TLAFile(String parent, String child, FilenameToStream fts) {
			super(parent,
				  ((ROOT_PATH_PATTERN.matcher(parent).find() && child.startsWith(parent))
						  ? child.substring(parent.length())
					      : child));
			this.libraryPath = this.exists() ? this.toURI() : null;
			this.isLibraryModule = false;
			this.resolver = fts;
		}

		public TLAFile(String pathname, URL location, boolean isLibraryModule, FilenameToStream fts) {
			super(pathname);
			// Do not check exists here like in the other ctors because it returns false
			// before the file is actually read in util.SimpleFilenameToStream.read(String,
			// URL, InputStream). Instead, assume that the file exists if we get here. After
			// all, we know that its inputstream exists.
			// If the conversion from URL to URI fails, we continue with null an hope that
			// everything goes fine.
			this.libraryPath = toNullOrURI(location);
			this.isLibraryModule = isLibraryModule;
			this.resolver = fts;
		}

		public TLAFile(Path path, URL location, boolean isLibraryModule, FilenameToStream fts) {
			this(path.toFile().toString(), location, isLibraryModule, fts);
		}

		private static URI toNullOrURI(URL location) {
	  		try {
	  			return location.toURI();
	  		} catch (URISyntaxException e) {
	  			return null;
	        }
		}

		public boolean isLibraryModule() {
			return isLibraryModule;
		}

		/**
		 * @return null if no TLC module override for this module exists.
		 */
		public File getModuleOverride() {
			final File moduleOverride = resolver.resolve(getName().replaceAll(".tla$", ".class"), false);
			if (moduleOverride.exists()) {
				// resolve(...) return a File instance even if the file doesn't exist.
				return moduleOverride;
			}
			return null;
		}

		/**
		 * This method enables us to keep track of the original path (or library) 
		 * of the module.
		 */
		public URI getLibraryPath() {
			return libraryPath;
		}

		public boolean hasLibraryPath() {
			return libraryPath != null;
		}
	}
	
    /**
     * This method resolves the logical name to the OS-resource
     * @param filename
     * @param isModule
     * @return
     */
    public File resolve(String filename, boolean isModule);

      /**
       * August 2014 - TL
       * Added this method which returns all the path locations stored in the resolver
      */
    public String getFullPath();

    /**
     * Returns true iff moduleName is the name of a standard module, which
     * is identified by the directory in which its source file resides.
     *
     * @param moduleName
     * @return
	 * @see tla2sany.modanalyzer.ParseUnit.isLibraryModule()
	 * @see StandardModules.isDefinedInStandardModule()
     */
    public boolean isStandardModule(String moduleName) ;

	default boolean isLibraryModule(String moduleName) {
		return isStandardModule(moduleName);
	}
 	
	static boolean isInJar(final String aString) {
		return aString.startsWith("jar:") || aString.endsWith(".jar");
	}

	static boolean isArchive(String aString) {
		return isInJar(aString) || aString.endsWith(".zip");
	}
	
	static Path getTempDirectory() {
  		try {
			return Files.createTempDirectory("tlc-");
		} catch (IOException e) {
			// This is unfortunately how we handle things over here. :-(
			e.printStackTrace();
		}
  		return null;
	}
}
