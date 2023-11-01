// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2023, Oracle and/or its affiliates.
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

    /**
     * Higher layers of TLC (and the Toolbox) have to determine if a module was
     * loaded from a library location s.a. those defined by TLA_LIBRARY (see
     * SimpleFilenameToStream). Thus, capture this information at module load
     * time when it is known where a module was loaded from.
     */
    @SuppressWarnings("serial")
    public static class TLAFile extends File {
        /**
         * The following regex is concerned with determining whether the provided 'parent' string to our
         *parent/child constructor looks like the start of a legal absolute file path potentially including
         *a drive letter.
         */
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
     * Resolves a logical name to a concrete OS-resource.
     *
     * @param filename a logical name (e.g. <code>"Integers"</code>) or path (e.g. <code>"subdir/Integers.tla"</code>)
     * @param isModule if true and the given filename does not end with {@link TLAConstants.Files#TLA_EXTENSION}, then
     *                 the extension will be added.  Also, if the extension was already present, it will be converted
     *                 to the correct case.  If <code>isModule</code> is false, then <code>filename</code> will be
     *                 resolved unaltered.
     * @return a local file containing the module source, or a non-null non-existent file if the name was not found
     */
    // TODO: improve the performance of this interface.
    // Returning a File is overly restrictive: some implementations resolve from non-filesystem locations like inside
    // JARs.  To satisfy this interface, those implementations have to copy the resolved resource to a local file.
    // That copy could be avoided if this interface returned a less restrictive type like NamedInputStream.
    File resolve(String filename, boolean isModule);

    /**
     * Get a string describing the path locations this resolver will search.  The result has no particular format;
     * it is intended for user-facing error output and debugging.
     *
     * @return a string describing the searched locations
     * @since August 2014 - TL
     */
    String getFullPath();

    /**
     * Returns true iff <code>moduleName</code> resolves to a standard module.  The argument is treated the same as a
     * call to {@link #resolve(String, boolean)} with <code>isModule=true</code>.
     *
     * @param moduleName the name of a module (e.g. <code>"Integers"</code>)
     * @return true iff <code>moduleName</code> names a standard module
     * @see tla2sany.modanalyzer.ParseUnit#isLibraryModule()
     * @see tla2sany.semantic.StandardModules#isDefinedInStandardModule(String)
     */
    boolean isStandardModule(String moduleName);

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
