// Copyright (c) 2025, Oracle and/or its affiliates.

package util;

import java.io.IOException;
import java.net.URL;

/**
 * Searches the Java classpath using {@link ClassLoader#getResource(String)}.  It takes a /-separated prefix that is
 * prepended to the search, e.g. <code>"tla2sany/StandardModules"</code>.  Extra '/' characters at the end of the
 * prefix have no effect.  The search is not recursive.
 */
class ClasspathResourceLocator implements ResourceLocator {

    private final ClassLoader classLoader;
    private final String prefix;

    public ClasspathResourceLocator(ClassLoader classLoader, String prefix) {
        while (prefix.endsWith("/")) {
            prefix = prefix.substring(0, prefix.length() - 1);
        }
        this.classLoader = classLoader;
        this.prefix = prefix;
    }

    @Override
    public URL locate(String filename) throws IOException {
        return classLoader.getResource(prefix.isEmpty() ? filename : prefix + "/" + filename);
    }

    @Override
    public String describeSearchLocations() {
        return "classpath:/" + prefix;
    }

}
