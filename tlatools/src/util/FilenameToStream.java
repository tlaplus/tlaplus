// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package util;

import java.io.File;
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
		private static final String ROOT_PATH_REGEX
								= "^([A-Z]+:)?" + ((File.separatorChar == '\\') ? "\\\\" : File.separator);
		private static final Pattern ROOT_PATH_PATTERN = Pattern.compile(ROOT_PATH_REGEX);
		
		
		private final boolean isLibraryModule;
		private transient final FilenameToStream resolver;

		public TLAFile(String pathname, FilenameToStream fts) {
			this(pathname, false, fts);
		}

		public TLAFile(String pathname, boolean isLibraryModule, FilenameToStream fts) {
			super(pathname);
			this.isLibraryModule = isLibraryModule;
			this.resolver = fts;
		}

		public TLAFile(String parent, String child, FilenameToStream fts) {
			super(parent,
				  ((ROOT_PATH_PATTERN.matcher(parent).find() && child.startsWith(parent))
						  ? child.substring(parent.length())
					      : child));
			this.isLibraryModule = false;
			this.resolver = fts;
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
   
	static final String TMPDIR = System.getProperty("java.io.tmpdir");

	static boolean isInJar(final String aString) {
		return aString.startsWith("jar:") || aString.endsWith(".jar");
	}

	static boolean isArchive(String aString) {
		return isInJar(aString) || aString.endsWith(".zip");
	}
}
