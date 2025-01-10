// Copyright (c) 2025, Oracle and/or its affiliates.

package util;

import java.io.IOException;
import java.net.URL;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * Searches a filesystem path.  The search is not recursive.  Note that this class may explore outside its prefix
 * if the target is an absolute path; the search behaves like {@link Path#resolve(Path)}.
 */
class FilesystemResourceLocator implements ResourceLocator {

    private final Path prefix;

    public FilesystemResourceLocator(Path prefix) {
        this.prefix = prefix;
    }

    @Override
    public URL locate(String filename) throws IOException {
        Path result = prefix.resolve(filename);
        return Files.exists(result) ? result.toUri().toURL() : null;
    }

    @Override
    public String describeSearchLocations() {
        return prefix.toString();
    }

}
