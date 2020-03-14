// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:28 PST by lamport
//      modified on Mon Jan 29 16:21:11 PST 2001 by yuanyu

package tlc2.tool.impl;

import java.io.File;
import java.net.URL;
import java.net.URLClassLoader;

import tlc2.output.EC;
import util.Assert;
import util.FilenameToStream;

/**
 * 
 * @author Yuan Yu, Simon Zambrovski
 * @version $Id$
 */
public class TLAClass
{
    /* Load a class from a file. */
    private final String pkg;
	private final FilenameToStream resolver;

    public TLAClass(String pkg, FilenameToStream resolver)
    {
        this.resolver = resolver;
		if (pkg.length() != 0 && pkg.charAt(pkg.length() - 1) != '.')
        {
            this.pkg = pkg + '.';
        } else
        {
            this.pkg = pkg;
        }
    }

	/**
	 * This method attempts to load the java class with the given name.
	 * 
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
    public synchronized Class loadClass(String name)
    {
        Class cl = null;
        try
        {
        	try {
        		if (resolver != null) {
        			final File module = resolver.resolve(name + ".class", false);
        			if (module != null && module.getAbsoluteFile() != null) {
        				final URL url = module.getAbsoluteFile().getParentFile().toURI().toURL();
        				cl = new URLClassLoader(new URL[] {url}).loadClass(name);
        			}
        		}
        	} catch (Exception ignored1) {
        		/*SKIP*/
        	} finally {
        		if (cl == null) {
        			try
        			{
        				cl = Class.forName(name);
        			} catch (Exception e)
        			{ /*SKIP*/
        			}
        		}
        	}
            if (cl == null)
            {
                try
                {
                    cl = Class.forName(this.pkg + name);
                } catch (Exception e)
                { /*SKIP*/
                }
            }
        } catch (Throwable e)
        {
            Assert.fail(EC.TLC_ERROR_REPLACING_MODULES, new String[] { name, 
                       (e.getMessage()==null)?e.toString():e.getMessage() });
        }
        return cl;
    }
    
//
//    public static void main(String argv[])
//    {
//        TLAClass tc = new TLAClass("tlc2.module");
//        Class c = tc.loadClass("Strings"); // must set CLASSPATH correctly
//        System.err.println("c = " + c);
//        // Class c1 = tc.loadClass("Class");
//        // System.err.println("c1 = " + c1);
//    }
//
}
