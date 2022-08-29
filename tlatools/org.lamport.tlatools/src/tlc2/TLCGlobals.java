// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tlc2;

import java.io.File;
import java.net.URISyntaxException;
import java.net.URL;
import java.text.DateFormat;
import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Enumeration;
import java.util.Objects;
import java.util.TimeZone;
import java.util.jar.Attributes;
import java.util.jar.Manifest;

/**
 * Globals
 *
 * @author Leslie Lamport
 * @author Yuan Yu
 * @author Simon Zambrovski
 * @author Markus A. Kuppe
 */
public class TLCGlobals {

    public static final int DEFAULT_CHECKPOINT_DURATION = (30 * 60 * 1000) + 42;

    // The current version of TLC
    public static final String versionOfTLC = "Version 2.18 of Day Month 20??";
    public static final double livenessGraphSizeThreshold = 0.1d;
    /**
     * Ratio of runtime dedicated to safety checking (80%) and liveness checking
     * (20%). Some aspects of liveness are also checked during state insertion
     * (see ILiveCheck#addNextState) and thus part of safety checking..
     */
    public static final double livenessRatio = 0.2d;
    // Char to indent nested coverage information.
    public static final char coverageIndent = '|';
    // The time interval to report progress (in milliseconds)
    public static final int progressInterval = 1 * 60 * 1000;
    // The meta data root.
    public static final String metaRoot = "states";
    // The bound for set enumeration, used for pretty printing
    public static int enumBound = 2000;
    // The bound for the cardinality of a set
    public static int setBound = 1000000;
    /**
     * Execute liveness checking when any of the disk graphs' size has increased
     * exceeding the threshold (10% by default).
     */
    public static double livenessThreshold = 0.1d;
    public static String lnCheck = "default";
    // Enable collecting coverage information
    public static int coverageInterval = -1;
    // Continue running even when invariant is violated
    public static boolean continuation = false;
    // Prints only the state difference in state traces
    public static boolean printDiffsOnly = false;
    // Suppress warnings report if true
    public static boolean warn = true;
    // The time interval to checkpoint. (in milliseconds)
    public static long chkptDuration = Integer.getInteger(
            TLCGlobals.class.getName() + ".chkpt", DEFAULT_CHECKPOINT_DURATION);
    // MAK 08.2012: centralized checkpoint code and added disabling and
    // externally forced checkpoints
    public static boolean forceChkpt = false;
    public static String metaDir = null;
    // The flag to control if VIEW is applied when printing out states.
    public static boolean useView = false;
    // The flag to control if gzip is applied to Value input/output stream.
    public static boolean useGZIP = false;
    // debugging field
    public static boolean debug = false;
    // format messages easy for parsing
    public static boolean tool = false;
    public static boolean expand = true;
    // Number of concurrent workers
    private static int numWorkers = 1;

    public static boolean doLiveness() {
        return !(lnCheck.equals("final") || lnCheck.equals("seqfinal"));
    }

    public static boolean doSequentialLiveness() {
        return lnCheck.startsWith("seq");
    }

    public static synchronized int getNumWorkers() {
        return numWorkers;
    }

    public static synchronized void setNumWorkers(final int n) {
        numWorkers = n;
    }

    public static synchronized void incNumWorkers(final int n) {
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

    public static boolean isCoverageEnabled() {
        return coverageInterval >= 0;
    }

    public static void forceChkpt() {
        forceChkpt = true;
    }

    public static boolean chkptExplicitlyEnabled() {
        // Assumption is that a user will always select a different value.
        return chkptDuration > 0 && chkptDuration != DEFAULT_CHECKPOINT_DURATION;
    }

    public static void reset() {
        numWorkers = 1;
        livenessThreshold = 0.1d;
        lnCheck = "default";
        coverageInterval = -1;
        continuation = false;
        printDiffsOnly = false;
        warn = true;
        chkptDuration = Integer.getInteger(
                TLCGlobals.class.getName() + ".chkpt", DEFAULT_CHECKPOINT_DURATION);
        forceChkpt = false;
        metaDir = null;
        useView = false;
        useGZIP = false;
        debug = false;
        tool = false;
        expand = true;
    }

    public static boolean isValidSetSize(final int bound) {
        return bound >= 1;
    }

    public static String getRevision() {
        return getManifestValue("X-Git-ShortRevision");
    }

    public static String getRevisionOrDev() {
        return TLCGlobals.getRevision() == null ? "development" : TLCGlobals.getRevision();
    }

    public static Date getBuildDate() {
        try {
            final String manifestValue = getManifestValue("Build-TimeStamp");
            if (manifestValue == null) {
                return new Date();
            }
            final DateFormat df = new SimpleDateFormat("yyyy-MM-dd'T'HH:mm:ss.S'Z'");
            df.setTimeZone(TimeZone.getTimeZone("UTC"));
            // TLC's Build-TimeStamp in the jar's Manifest is format according to ISO 8601
            // (https://en.m.wikipedia.org/wiki/ISO_8601)
            return df.parse(manifestValue);
        } catch (final NullPointerException | ParseException e) {
            // There is no manifest or the manifest does not contain a build time stamp, in
            // which case we return the current, syntactically equivalent time stamp.
            // This is usually the case when running TLC from an IDE or the 'test' target of
            // the Ant custombuild.xml file. In other words, this occurs during TLC development.
            // However, regular usage should not take this branch.
            // https://en.m.wikipedia.org/wiki/ISO_8601
            return new Date();
        }
    }

    public static int getSCMCommits() {
        try {
            return Integer.parseInt(Objects.requireNonNull(getManifestValue("X-Git-Commits-Count")));
        } catch (final NullPointerException | NumberFormatException nfe) {
            // Not mapping to -1 so that at the level of TLA+ it is \in Nat.
            return 0;
        }
    }

    private static String getManifestValue(final String key) {
        try {
            final Enumeration<URL> resources = TLCGlobals.class.getClassLoader().getResources("META-INF/MANIFEST.MF");
            while (resources.hasMoreElements()) {
                final Manifest manifest = new Manifest(resources.nextElement().openStream());
                final Attributes attributes = manifest.getMainAttributes();
                if ("TLA+ Tools".equals(attributes.getValue("Implementation-Title"))) {
                    if (attributes.getValue(key) != null) {
                        return attributes.getValue(key);
                    } else {
                        return null;
                    }
                }
            }
        } catch (final Exception ignore) {
        }
        return null;
    }

    public static String getInstallLocation() {
        try {
            return new File(TLC.class.getProtectionDomain().getCodeSource().getLocation().toURI()).getPath();
        } catch (final URISyntaxException e) {
            return "unknown";
        }
    }
}
