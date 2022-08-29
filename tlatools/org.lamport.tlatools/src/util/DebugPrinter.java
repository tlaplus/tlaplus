package util;

import tlc2.TLCGlobals;

/**
 * Debugging helper
 *
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DebugPrinter {
    /**
     * Prints out a message if the program has been called with -debug option
     */
    public static void print(final String message) {
        if (TLCGlobals.debug) {
            System.out.println(Thread.currentThread().getId() + "\t" + message);
        }
    }

    /**
     * Exception stacktrace printer
     */
    public static void print(final Throwable e) {
        if (TLCGlobals.debug) {
            System.err.println(Thread.currentThread().getId() + "thrown an exception");
            e.printStackTrace(System.err);
        }
    }


}
