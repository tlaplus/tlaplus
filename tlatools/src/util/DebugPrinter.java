package util;

import tlc2.TLCGlobals;

/**
 * Debugging helper
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DebugPrinter
{
    /**
     * Prints out a message if the program has been called with -debug option 
     * @param message
     */
    public static void print(String message)
    {
        if (TLCGlobals.debug) 
        {
            System.out.println(Thread.currentThread().getId() + "\t" + message);
        }
    }

    /**
     * Exception stacktrace printer
     * @param e
     */
    public static void print(Throwable e)
    {
        if (TLCGlobals.debug) 
        {
            System.err.println(Thread.currentThread().getId() + "thrown an exception");
            e.printStackTrace(System.err);
        }
    }

    
}
