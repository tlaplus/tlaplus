package util;

import tlc2.TLCGlobals;

/**
 * Debugging helper
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DebugReporter
{
    /**
     * Prints out a message if the program has been called with -debug option 
     * @param message
     */
    public static void report(String message)
    {
        if (TLCGlobals.debug) 
        {
            System.err.println(Thread.currentThread().getId() + "\t" + message);
        }
    }

    /**
     * Exception stacktrace printer
     * @param e
     */
    public static void report(Throwable e)
    {
        if (TLCGlobals.debug) 
        {
            System.err.println(Thread.currentThread().getId() + "thrown an exception");
            e.printStackTrace(System.err);
        }
    }

    
}
