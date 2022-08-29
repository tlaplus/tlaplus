// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:28 PST by lamport
//      modified on Mon Jan 29 16:21:11 PST 2001 by yuanyu

package tlc2.tool.impl;

import tlc2.output.EC;
import util.Assert;
import util.FilenameToStream;

import java.io.File;
import java.net.URL;
import java.net.URLClassLoader;

/**
 * @author Yuan Yu, Simon Zambrovski
 * @version $Id$
 */
public class TLAClass {
    /* Load a class from a file. */
    private final String pkg;
    private final FilenameToStream resolver;

    public TLAClass(final String pkg, final FilenameToStream resolver) {
        this.resolver = resolver;
        if (pkg.length() != 0 && pkg.charAt(pkg.length() - 1) != '.') {
            this.pkg = pkg + '.';
        } else {
            this.pkg = pkg;
        }
    }

    /**
     * This method attempts to load the java class with the given name.
     * <p>
     * Loading classes is done in three steps:
     *
     * <ul>
     * <li>1) TLC's {@link FilenameToStream} resolver is used to locate a class
     * file in the resolver's lookup path. Check {@link FilenameToStream}'s
     * documentation on the lookup order. If a class file with name "name.class"
     * can be found, it is loaded.</li>
     * <li>2) With the unqualified name, we try to lookup the class in the
     * regular VM's CLASSPATH.</li>
     * <li>3) As a last resort, we try to load a class fully qualified with the
     * package name given in {@link TLAClass#pkg}.</li>
     * </ul>
     * <p>
     * If no class could be loaded, <code>null</code> is returned.
     **/
    public synchronized Class<?> loadClass(final String name) {
        Class<?> cl = null;

        try {
            try {
                if (resolver != null) {
                    final File module = resolver.resolve(name + ".class", false);
                    if (module != null) {
                        module.getAbsoluteFile();
                        final URL url = module.getAbsoluteFile().getParentFile().toURI().toURL();
                        try(final var classLoader = new URLClassLoader(new URL[]{url})) {
                            cl = classLoader.loadClass(name);
                        }
                    }
                }
            } catch (final Exception ignored1) {
                /*SKIP*/
            } finally {
                if (cl == null) {
                    try {
                        cl = Class.forName(name);
                    } catch (final Exception e) { /*SKIP*/
                    }
                }
            }
            if (cl == null) {
                try {
                    cl = Class.forName(this.pkg + name);
                } catch (final Exception e) { /*SKIP*/
                }
            }
        } catch (final Throwable e) {
            Assert.fail(EC.TLC_ERROR_REPLACING_MODULES, new String[]{name,
                    (e.getMessage() == null) ? e.toString() : e.getMessage()});
        }
        return cl;
    }

}
