/***************************************************************************
* How to get the current directory.                                        *
*                                                                          *
* Also, all the java (version 1.5) properties.                             *
***************************************************************************/
package tlc2.tool.other;

import java.io.File;

/**
 * Simple printing utility
 * @deprecated is likely not used (SZ February 19, 2009)
 */
public class CurrentDir
{
    public static void main(String args[])
    {
        for (int i = 0; i < args.length; i++)
        {
            System.out.println("args[" + i + "] = '" + args[i] + "'");
        }
        ;

        File dir1 = new File(".");
        File dir2 = new File("..");
        try
        {
            System.out.println("Current dir : " + dir1.getCanonicalPath());
            System.out.println("Parent  dir : " + dir2.getCanonicalPath());
            System.out.println("HOME: " + System.getenv("HOME"));
            // System.out.println("user.home: " + System.getProperty("user.home")) ;
            System.out.println("java.version : " + System.getProperty("java.version"));
            System.out.println("java.vendor : " + System.getProperty("java.vendor"));
            System.out.println("java.vendor.url : " + System.getProperty("java.vendor.url"));
            System.out.println("java.home : " + System.getProperty("java.home"));
            System.out
                    .println("java.vm.specification.version : " + System.getProperty("java.vm.specification.version"));
            System.out.println("java.vm.specification.vendor : " + System.getProperty("java.vm.specification.vendor"));
            System.out.println("java.vm.specification.name : " + System.getProperty("java.vm.specification.name"));
            System.out.println("java.vm.version : " + System.getProperty("java.vm.version"));
            System.out.println("java.vm.vendor : " + System.getProperty("java.vm.vendor"));
            System.out.println("java.vm.name : " + System.getProperty("java.vm.name"));
            System.out.println("java.specification.version : " + System.getProperty("java.specification.version"));
            System.out.println("java.specification.vendor : " + System.getProperty("java.specification.vendor"));
            System.out.println("java.specification.name : " + System.getProperty("java.specification.name"));
            System.out.println("java.class.version : " + System.getProperty("java.class.version"));
            System.out.println("java.class.path : " + System.getProperty("java.class.path"));
            System.out.println("java.library.path : " + System.getProperty("java.library.path"));
            System.out.println("java.io.tmpdir : " + System.getProperty("java.io.tmpdir"));
            System.out.println("java.compiler : " + System.getProperty("java.compiler"));
            System.out.println("java.ext.dirs : " + System.getProperty("java.ext.dirs"));
            System.out.println("os.name : " + System.getProperty("os.name"));
            System.out.println("os.arch : " + System.getProperty("os.arch"));
            System.out.println("os.version : " + System.getProperty("os.version"));
            System.out.println("file.separator : " + System.getProperty("file.separator"));
            System.out.println("path.separator : " + System.getProperty("path.separator"));
            System.out.println("line.separator : " + System.getProperty("line.separator"));
            System.out.println("user.name : " + System.getProperty("user.name"));
            System.out.println("user.home : " + System.getProperty("user.home"));
            System.out.println("user.dir : " + System.getProperty("user.dir"));

            System.out.println("Setting current directory to c:\\users\\lamport");
            System.setProperty("user.dir", "c:\\users\\lamport");
            System.out.println("user.dir : " + System.getProperty("user.dir"));
            System.out.println("Current dir : " + dir1.getCanonicalPath());

        } catch (Exception e)
        {
            e.printStackTrace();
        }
    }
}
