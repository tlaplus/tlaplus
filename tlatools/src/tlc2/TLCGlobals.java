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
    public static String versionOfTLC = "Version 2.05 of 23 July 2013";

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
    
    /**
     * Increments the number of workers by 1
     */
    public static void incNumWorkers() {
    	incNumWorkers(1);
    }
    
    /**
     * Decrements the number of workers by 1
     */
    public static void decNumWorkers() {
    	incNumWorkers(-1);
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
	public static long chkptDuration = Integer.getInteger(
			TLCGlobals.class.getName() + ".chkpt", 30 * 60 * 1000);
    
	// MAK 08.2012: centralized checkpoint code and added disabling and
	// externally forced checkpoints
    private static boolean forceChkpt = false;
    public static void forceChkpt() {
    	forceChkpt = true;
    }
    private static long lastChkpt = System.currentTimeMillis();
    
	/**
	 * IMPORTANT NOTE: The method is unsynchronized. It is the caller's
	 * responsibility to ensure that only a single thread calls this method.
	 * 
	 * @return true iff a checkpoint should be created next time possible
	 */
    public static boolean doCheckPoint() {
    	// 1. checkpoint forced externally (e.g. JMX)
    	if (forceChkpt) {
    		forceChkpt = false;
    		return true;
    	}
    	
    	// 2. user has disabled checkpoints
    	if (chkptDuration == 0) {
    		return false;
    	}
    	
    	// 3. time between checkpoints is up?
        long now = System.currentTimeMillis();
        if (now - lastChkpt >= TLCGlobals.chkptDuration) {
        	lastChkpt = now;
        	return true;
        }
        return false;
    }

    // The meta data root.
    public static final String metaRoot = "states";
    public static String metaDir = null;

    // The flag to control if VIEW is applied when printing out states.
    public static boolean useView = false;

    // The flag to control if gzip is applied to Value input/output stream.
    public static boolean useGZIP = true;

    // The tool id number for TLC2.
    public static int ToolId = FrontEnd.getToolId();

    // debugging field
    public static boolean debug = false;

    // format messages easy for parsing
    public static boolean tool = false;

	public static boolean isValidSetSize(final int bound) {
		if (bound < 1) {
			return false;
		}
		return true;
	}
}
