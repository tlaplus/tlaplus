// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2;

import java.net.URL;
import java.util.Enumeration;
import java.util.jar.Attributes;
import java.util.jar.Manifest;

import tlc2.tool.AbstractChecker;
import tlc2.tool.Simulator;

/**
 * Globals
 * @author Leslie Lamport
 * @author Yuan Yu
 * @author Simon Zambrovski
 * @author Markus A. Kuppe
 */
public class TLCGlobals
{

	public static final int DEFAULT_CHECKPOINT_DURATION = (30 * 60 * 1000) + 42;

	// The current version of TLC
    public static String versionOfTLC = "Version 2.15 of Day Month 20??";
    
    // The bound for set enumeration, used for pretty printing
    public static int enumBound = 2000;
    
    // The bound for the cardinality of a set
    public static int setBound = 1000000;

    // Number of concurrent workers
    private static int numWorkers = 1;
    
	/**
	 * Execute liveness checking when any of the disk graphs' size has increased
	 * exceeding the threshold (10% by default).
	 */
    public static double livenessThreshold = 0.1d;

    public static double livenessGraphSizeThreshold = 0.1d;

	/**
	 * Ratio of runtime dedicated to safety checking (80%) and liveness checking
	 * (20%). Some aspects of liveness are also checked during state insertion
	 * (see ILiveCheck#addNextState) and thus part of safety checking..
	 */
	public static double livenessRatio = 0.2d;
	
	public static String lnCheck = "default";
	
	public static boolean doLiveness() {
		return !(lnCheck.equals("final") || lnCheck.equals("seqfinal"));
	}

	public static boolean doSequentialLiveness() {
		return lnCheck.startsWith("seq");
	}

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

    // The main model checker object (null if simulator non-null)
    public static AbstractChecker mainChecker = null;
    
    // The main simulator object (null if mainChecker non-null)
    public static Simulator simulator = null;

    // Char to indent nested coverage information.
	public static final char coverageIndent = '|';
    
    // Enable collecting coverage information
    public static int coverageInterval = -1;

    public static final boolean isCoverageEnabled() {
    	return coverageInterval >= 0;
    }
    
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
			TLCGlobals.class.getName() + ".chkpt", DEFAULT_CHECKPOINT_DURATION);
    
	// MAK 08.2012: centralized checkpoint code and added disabling and
	// externally forced checkpoints
    private static boolean forceChkpt = false;
    public static void forceChkpt() {
    	forceChkpt = true;
    }
    private static long lastChkpt = System.currentTimeMillis();

	public static boolean chkptExplicitlyEnabled() {
		// Assumption is that a user will always select a different value.
		return chkptDuration > 0 && chkptDuration != DEFAULT_CHECKPOINT_DURATION;
	}

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
    public static boolean useGZIP = false;

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
	
	public static String getRevision() {
		try {
			final Enumeration<URL> resources = TLCGlobals.class.getClassLoader().getResources("META-INF/MANIFEST.MF");
			while (resources.hasMoreElements()) {
				final Manifest manifest = new Manifest(resources.nextElement().openStream());
				final Attributes attributes = manifest.getMainAttributes();
				if("TLA+ Tools".equals(attributes.getValue("Implementation-Title"))) {
					if(attributes.getValue("X-Git-ShortRevision") != null) {
						return attributes.getValue("X-Git-ShortRevision");
					} else {
						return null;
					}
				}
			}
		} catch (Exception ignore) {
		}
		return null;
	}
	
	public static String getRevisionOrDev() {
		return TLCGlobals.getRevision() == null ? "development" : TLCGlobals.getRevision();
	}

	public static boolean expand = true;
}
