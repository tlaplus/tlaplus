// Copyright (c) 2025, Oracle and/or its affiliates.

package util;

import java.io.IOException;
import java.net.URL;
import java.util.List;

/**
 * Converts abstract filenames (e.g. <code>"Integers.tla"</code>) to concrete locations
 * (e.g. <code>"jar:file:/path/to/tla2tools.jar!/tla2sany/StandardModules/Integers.tla"</code>).
 *
 * <p>This interface is simple enough to be composable: multiple locators can be chained together
 * using {@link SequentialResourceLocator}.
 */
interface ResourceLocator {

    /**
     * Searches no locations; fails to locate all files.
     */
    public static final ResourceLocator EMPTY = new SequentialResourceLocator(List.of());

    /**
     * Locate the given file.  The name is treated as a filename, not a TLA+ module name;
     * if you are looking for the Integers module, pass <code>"Integers.tla"</code>.
     *
     * @param filename the file to locate, e.g. <code>"Integers.tla"</code>
     * @return a URL to the file, or <code>null</code> if it could not be found
     * @throws IOException if an error occurs while searching
     */
    URL locate(String filename) throws IOException;

    /**
     * Get a human-readable string describing the locations that {@link #locate(String)} will search.
     *
     * @return a description of the search locations
     */
    String describeSearchLocations();

}
