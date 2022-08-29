// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import org.junit.Test;
import org.junit.experimental.categories.Category;
import tla2sany.semantic.OpDeclNode;
import tlc2.tool.TLCState;
import tlc2.tool.TLCTrace;
import tlc2.tool.queue.DummyTLCState;
import util.LongTest;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public abstract class AbstractHeapBasedDiskFPSetTest {

    /* Test the lower limits */

    @Test
    public void testCtorLLMinus1() throws Exception {
        doTest(getLowerLimit() - 1);
    }

    @Test
    public void testCtorLL() throws Exception {
        doTest(getLowerLimit());
    }

    @Test
    public void testCtorLLPlus1() throws Exception {
        doTest(getLowerLimit() + 1);
    }

    @Test
    public void testCtorLLNextPow2Min1() throws Exception {
        doTest((getLowerLimit() << 1) - 1);
    }

    /* Test with a power far away from upper/lower limits */

    @Test
    public void testCtorPow16Minus1() throws Exception {
        doTest((1L << 16) - 1);
    }

    @Test
    public void testCtorPow16() throws Exception {
        doTest(1L << 16);
    }

    @Test
    public void testCtorPow16Plus1() throws Exception {
        doTest((1L << 16) + 1);
    }

    @Test
    public void testCtorPow16NextPow2Min1() throws Exception {
        doTest(((1L << 16) << 1) - 1);
    }

    /* Test the upper limits */

    @Test
    public void testCtorULMinus1() throws Exception {
        doTest(getUpperLimit() - 1);
    }

    @Test
    public void testCtorUL() throws Exception {
        doTest(getUpperLimit());
    }

    @Test
    public void testCtorULPlus1() throws Exception {
        doTest(getUpperLimit() + 1);
    }

    @Test
    public void testCtorULNextPow2Min1() throws Exception {
        doTest((getUpperLimit() << 1) - 1);
    }

    @Category(LongTest.class)
    @Test
    public void testFPSetRecovery() throws Exception {
        final int limit = 99999;
        final String metadir = System.getProperty("java.io.tmpdir");
        final String filename = this.getClass().getCanonicalName();

        // First, create a trace file to recover from.
        final TLCTrace trace = new TLCTrace(metadir, filename,
                null);

        // Fill the trace file with random fingerprints
        final TLCState predecessor = new DummyTLCState(new OpDeclNode[]{});
        predecessor.uid = 1L;
        // an init state
        trace.writeState(predecessor.uid);
        // successor states
        for (long fp = predecessor.uid + 1; fp < limit; fp++) {
            trace.writeState(predecessor, fp);
            predecessor.uid = fp;
        }

        // Create a checkpoint file
        trace.beginChkpt();
        trace.commitChkpt();

        // Create a DiskFPSet
        final DiskFPSet fpSet = getDiskFPSet(new FPSetConfiguration());
        fpSet.init(1, metadir, filename);
        fpSet.recover(trace);

        // Verify successful recovery
        assertEquals(limit - 1, fpSet.size());
        for (long fp = 1L; fp < limit; fp++) {
            assertTrue(fpSet.contains(fp));
        }

        fpSet.close();
    }

    @Category(LongTest.class)
    @Test
    public void testFPSetRecovery2() throws Exception {
        final String metadir = System.getProperty("java.io.tmpdir");
        final String filename = this.getClass().getCanonicalName() + "testFPSetRecovery2";

        final DiskFPSet fpSet = getDiskFPSet(new FPSetConfiguration());
        fpSet.init(1, metadir, filename);

        // Make sure the FPSet tries to flush to disk.
        fpSet.forceFlush();

        for (long fp = 1; fp <= 1024; fp++) {
            fpSet.recoverFP(fp);
        }

        fpSet.close();
    }

    /* Helper */

    @SuppressWarnings("deprecation")
    protected void doTest(final long physicalMemoryInBytes) throws Exception {
        final FPSetConfiguration fpSetConfig = new DummyFPSetConfiguration();
        fpSetConfig.setMemory(physicalMemoryInBytes);

        final DiskFPSet fpset = getDiskFPSet(fpSetConfig);
        final long maxTblCntInBytes = fpset.getMaxTblCnt() * FPSet.LongSize; // Convert from logical to physical

        // Always allocate less storage than given
        assertTrue("Internal storage exceeds allocated memory", physicalMemoryInBytes >= maxTblCntInBytes);

        // Storage with zero space for a fingerprint does make much sense, does it?
        assertTrue("Internal storage underflow allocated memory", 0L < maxTblCntInBytes);

        // We happen to know that LSBDiskFPSet reserves some memory to auxiliary
        // storage. Make this reservation the lower bound for the primary
        // storage. We div by 2 to account for the fact that both
        // implementations round down to the next power of 2.
        final double lowerLimit = (physicalMemoryInBytes / 2) / fpset.getAuxiliaryStorageRequirement();
        assertTrue("Internal storage falls short lower allocation limit", lowerLimit <= maxTblCntInBytes);

        fpset.close();
    }

    protected abstract DiskFPSet getDiskFPSet(final FPSetConfiguration fpSetConfig) throws Exception;

    /**
     * @return The lower size limit the {@link HeapBasedDiskFPSet} can handle.
     * It is determined by the implementation's
     * {@link DiskFPSet#getAuxiliaryStorageRequirement()}.
     */
    protected abstract long getLowerLimit();

    /**
     * @return The upper size limit the {@link HeapBasedDiskFPSet} can handle.
     */
    protected abstract long getUpperLimit();
}
