// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:28 PST by lamport
//      modified on Mon Jan 29 16:21:11 PST 2001 by yuanyu

package tlc2.tool;

import tlc2.output.EC;
import util.Assert;

/**
 * 
 * @author Yuan Yu, Simon Zambrovski
 * @version $Id$
 */
public class TLAClass
{
    /* Load a class from a file. */
    private String pkg;

    public TLAClass(String pkg)
    {
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
     **/
    public synchronized Class loadClass(String name)
    {
        Class cl = null;
        try
        {
            try
            {
                cl = Class.forName(name);
            } catch (Exception e)
            { /*SKIP*/
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

    public static void main(String argv[])
    {
        TLAClass tc = new TLAClass("tlc2.module");
        Class c = tc.loadClass("Strings"); // must set CLASSPATH correctly
        System.err.println("c = " + c);
        // Class c1 = tc.loadClass("Class");
        // System.err.println("c1 = " + c1);
    }

}
