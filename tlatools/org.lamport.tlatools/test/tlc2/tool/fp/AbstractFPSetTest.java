// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import org.junit.After;
import org.junit.Before;

import java.io.File;
import java.text.DecimalFormat;
import java.util.Date;

public abstract class AbstractFPSetTest {

    protected static final long RNG_SEED = 15041980L;

    protected static final String tmpdir = System.getProperty("java.io.tmpdir") + File.separator + "FPSetTest"
            + System.currentTimeMillis();
    protected static final String filename = "FPSetTestTest";
    protected static final DecimalFormat df = new DecimalFormat("###,###.###");
    protected static final DecimalFormat pf = new DecimalFormat("#.##");

    protected long previousTimestamp;
    protected long previousSize;
    protected long startTimestamp;
    protected Date endTimeStamp;


    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    @Before
    public void setUp() {
        // create temp folder
        File dir = new File(tmpdir);
        dir.mkdirs();

        previousTimestamp = startTimestamp = System.currentTimeMillis();
        previousSize = 0L;

        System.out.println("Test started at " + new Date());
    }

    /* (non-Javadoc)
     * @see junit.framework.TestCase#tearDown()
     */
    @After
    public void tearDown() {
        if (endTimeStamp == null) {
            endTimeStamp = new Date();
        }
        System.out.println("Test finished at " + endTimeStamp);
    }

    /**
     * @return A new {@link FPSet} instance
     */
    protected abstract FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws Exception;

    protected FPSet getFPSetInitialized() throws Exception {
        return getFPSetInitialized(1);
    }

    protected FPSet getFPSetInitialized(final int numThreads) throws Exception {
        final FPSet fpSet = getFPSet(new FPSetConfiguration());
        fpSet.init(numThreads, tmpdir, filename);

        if (fpSet instanceof final FPSetStatistic fpSetStats) {
            final long maxTblCnt = fpSetStats.getMaxTblCnt();
            System.out.println("Maximum FPSet table count is: "
                    + df.format(maxTblCnt) + " (approx: "
                    + df.format(maxTblCnt * FPSet.LongSize >> 20) + " GiB)");
            System.out.println("FPSet lock count is: " + fpSetStats.getLockCnt());
            System.out.println("FPSet bucket count is: " + fpSetStats.getTblCapacity());
        }

        System.out.println("Testing " + fpSet.getClass().getCanonicalName());
        return fpSet;
    }

    // insertion speed
    public void printInsertionSpeed(final FPSet fpSet) {
        // print every minute
        final long now = System.currentTimeMillis();
        final double factor = (now - previousTimestamp) / 60000d;
        if (factor >= 1d) {
            final long currentSize = fpSet.size();
            final long insertions = (long) ((currentSize - previousSize) * factor);
            if (fpSet instanceof final FPSetStatistic fpSetStatistics) {
                System.out.println(System.currentTimeMillis() + " s (epoch); " + df.format(insertions) + " insertions/min; " + pf.format(fpSetStatistics.getLoadFactor()) + " load factor");
            } else {
                System.out.println(System.currentTimeMillis() + " s (epoch); " + df.format(insertions) + " insertions/min");
            }
            previousTimestamp = now;
            previousSize = currentSize;
        }
    }

    public void printInsertionSpeed(final FPSet fpSet, final long start, final long end) {
        final long size = fpSet.size();
        // Normalize insertions to minutes.
        final long duration = Math.max(end - start, 1); //ms (avoid div-by-zero)
        final long insertions = (size / duration) * 60000L;
        if (fpSet instanceof final FPSetStatistic fpSetStatistics) {
            System.out.println(System.currentTimeMillis() + " s; " + df.format(insertions) + " insertions/min; " + pf.format(fpSetStatistics.getLoadFactor()) + " load factor");
        } else {
            System.out.println(System.currentTimeMillis() + " s (epoch); " + df.format(insertions) + " insertions/min");
        }
    }
}
