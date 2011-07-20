// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2;

import tla2sany.semantic.FrontEnd;
import tlc2.tool.ModelChecker;

/**
 * Globals
 * @author Leslie Lamport
 * @author Yuan Yu
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLCGlobals
{

    // The current version of TLC
    public static String versionOfTLC = "Version 2.03 of 20 July 2011";

    // The bound for set enumeration, used for pretty printing
    public static int enumBound = 2000;

    // The bound for the cardinality of a set
    public static int setBound = 1000000;

    // Number of concurrent workers
    private static int numWorkers = 1;

    public synchronized static void setNumWorkers(int n)
    {
        numWorkers = n;
    }

    public synchronized static int getNumWorkers()
    {
        return numWorkers;
    }

    public synchronized static void incNumWorkers(int n)
    {
        numWorkers += n;
    }

    // The main model checker object
    public static ModelChecker mainChecker = null;

    // Enable collecting coverage information
    public static int coverageInterval = -1;

    // Depth for depth-first iterative deepening
    public static int DFIDMax = -1;

    // Continue running even when invariant is violated
    public static boolean continuation = false;

    // Prints only the state difference in state traces
    public static boolean printDiffsOnly = false;

    // Suppress warnings report if true
    public static boolean warn = true;

    // The time interval to report progress (in milliseconds)
    public static final int progressInterval = 1 * 60 * 1000;

    // The time interval to checkpoint. (in milliseconds)
    public static long chkptDuration = 30 * 60 * 1000;

    // The meta data root.
    public static final String metaRoot = "states";
    public static String metaDir = null;

    // The flag to control if VIEW is applied when printing out states.
    public static boolean useView = false;

    // The flag to control if gzip is applied to Value input/output stream.
    public static boolean useGZIP = true;

    // The list of fingerprint servers.
    public static String[] fpServers = null;

    // The tool id number for TLC2.
    public static int ToolId = FrontEnd.getToolId();

    // debugging field
    public static boolean debug = false;

    // format messages easy for parsing
    public static boolean tool = false;

    /**
     * Method added to support multiple invocation of TLC
     * SZ Mar 9, 2009: REFACTOR this class will cause problems and should be converted into a dynamic instance
     */
    public static void reset()
    {
        DFIDMax = -1;
        coverageInterval = -1;
        mainChecker = null;
        numWorkers = 1;
        setBound = 1000000;
        enumBound = 2000;
        fpServers = null;
        useGZIP = true;
        useView = false;
        debug = false;
        tool = false;
        chkptDuration = 30 * 60 * 1000;
    }
}
