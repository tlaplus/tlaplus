// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import org.junit.Test;
import tlc2.util.LongVec;

import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.*;

public class ShortDiskFPSetTest extends AbstractFPSetTest {
    private static final boolean runKnownFailures = Boolean
            .getBoolean(ShortDiskFPSetTest.class.getName() + ".runKnown");
    /**
     * Used to make sure that each tests has a unique file name to prevent test
     * interference when deleting/renaming buffer files on windows during disc
     * flush.
     */
    private static int CNT = 0;

    /* (non-Javadoc)
     * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(FPSetConfiguration)
     */
    @Override
    protected FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws Exception {
        final DiskFPSet fpSet = new DummyDiskFPSet(fpSetConfig);
        fpSet.init(1, tmpdir, filename + CNT++);
        return fpSet;
    }

    /**
     * Tests if {@link DiskFPSet#diskLookup(long)} returns true for zero fp
     */
    @Test
    public void testWithoutZeroFP() throws Exception {
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());
        assertFalse("Succeeded to look up 0 fp", fpSet.contains(0L));
        fpSet.close();
    }

    /**
     * Tests if {@link DiskFPSet#diskLookup(long)} returns true for min fp
     */
    @Test
    public void testWithoutMinFP() throws Exception {
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());
        assertFalse("Succeeded to look up 0 fp", fpSet.contains(Long.MIN_VALUE));
        fpSet.close();
    }

    /**
     * Tests if {@link DiskFPSet#diskLookup(long)} returns true for max fp
     */
    @Test
    public void testWithoutMaxFP() throws Exception {
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());
        assertFalse("Succeeded to look up 0 fp", fpSet.contains(Long.MAX_VALUE));
        fpSet.close();
    }

    /**
     * Tests if {@link DiskFPSet#diskLookup(long)} accepts a 0 fp
     */
    @Test
    public void testZeroFP() throws Exception {
        // skip known failures which aren't likely to be fixed anytime soon
        // @see Bug #213 in general/bugzilla/index.html
        if (!runKnownFailures) {
            System.out
                    .println("Skipping test failing due to Bug #213 in general/bugzilla/index.html");
            return;
        }

        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());
        assertFalse(fpSet.put(0L));
        assertTrue("Failed to look up 0 fp", fpSet.contains(0L));
        fpSet.close();
    }

    /**
     * Tests if {@link DiskFPSet#diskLookup(long)} accepts a min fp
     */
    @Test
    public void testMinFP() throws Exception {
        // skip known failures which aren't likely to be fixed anytime soon
        // @see Bug #213 in general/bugzilla/index.html
        if (!runKnownFailures) {
            System.out
                    .println("Skipping test failing due to Bug #213 in general/bugzilla/index.html");
            return;
        }

        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());
        // zeroing the msb in DiskFPSet turns Long.Min_Value into 0
        assertFalse(fpSet.put(Long.MIN_VALUE));
        assertTrue("Failed to look up min fp", fpSet.contains(Long.MIN_VALUE));

        fpSet.close();
    }

    /**
     * Tests if {@link DiskFPSet#diskLookup(long)} accepts a min - 1  fp
     */
    @Test
    public void testMinMin1FP() throws Exception {
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());
        // zeroing the msb in DiskFPSet turns Long.Min_Value into 0
        assertFalse(fpSet.put(Long.MIN_VALUE - 1L));
        assertTrue("Failed to look up min fp", fpSet.contains(Long.MIN_VALUE - 1L));

        fpSet.close();
    }


    /**
     * Tests if {@link DiskFPSet#diskLookup(long)} accepts a -1 fp
     */
    @Test
    public void testNeg1FP() throws Exception {
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());
        assertFalse(fpSet.put(-1L));
        assertTrue("Failed to look up min fp", fpSet.contains(-1L));

        fpSet.close();
    }

    /**
     * Tests if {@link DiskFPSet#diskLookup(long)} accepts a +1 fp
     */
    @Test
    public void testPos1FP() throws Exception {
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());
        assertFalse(fpSet.put(1L));
        assertTrue("Failed to look up min fp", fpSet.contains(1L));

        fpSet.close();
    }

    /**
     * Tests if {@link DiskFPSet#diskLookup(long)} accepts a max fp
     */
    @Test
    public void testMaxFP() throws Exception {
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());
        assertFalse(fpSet.put(Long.MAX_VALUE));
        assertTrue("Failed to look up max fp", fpSet.contains(Long.MAX_VALUE));

        fpSet.close();
    }

    /**
     * Tries to call
     * {@link DiskFPSet#calculateMidEntry(long, long, double, long, long)} with
     * values causing a negative midEntry to be calculated.
     */
    @Test
    public void testValues() throws Exception {
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());

        final List<Long> loVals = new ArrayList<>();
        // no negative values (MSB stripped in DiskFPSet)
        // loVals.add(Long.MIN_VALUE);
        // loVals.add(Long.MIN_VALUE - 1l);
        // loVals.add(Long.MIN_VALUE / 2l);
        // loVals.add(-1l);

        loVals.add(0L); // zero valid fp
        loVals.add(1L);
        loVals.add(Long.MAX_VALUE / 2L);
        loVals.add(Long.MAX_VALUE - 1L);
        loVals.add(Long.MAX_VALUE);

        final List<Long> hiVals = new ArrayList<>();
        // no negative values (MSB stripped in DiskFPSet)
        // hiVals.add(Long.MIN_VALUE);
        // hiVals.add(Long.MIN_VALUE - 1l);
        // hiVals.add(Long.MIN_VALUE / 2l);
        // hiVals.add(-1l);

        hiVals.add(0L); // zero valid fp
        hiVals.add(1L);
        hiVals.add(Long.MAX_VALUE / 2L);
        hiVals.add(Long.MAX_VALUE - 1L);
        hiVals.add(Long.MAX_VALUE);

        final List<Long> fps = new ArrayList<>();
        // no negative values (MSB stripped in DiskFPSet)
        // fps.add(Long.MIN_VALUE);
        // fps.add(Long.MIN_VALUE - 1l);
        // fps.add(Long.MIN_VALUE / 2l);
        // fps.add(-1l);

        fps.add(0L);
        fps.add(1L);
        fps.add(Long.MAX_VALUE / 2L);
        fps.add(Long.MAX_VALUE - 1L);
        fps.add(Long.MAX_VALUE);

        final List<Long> loEntries = new ArrayList<>();
        loEntries.add(0L);
        loEntries.add(1L);
        // possible maximum due to impl. detail in DiskFPSet
        // (array index Integer.Max_Value)
        loEntries.add((long) Integer.MAX_VALUE * 1024);
        // theoretically loEntry can go up to Long.MAX_VALUE
        // loEntries.add(Long.MAX_VALUE - 1l);
        // loEntries.add(Long.MAX_VALUE);

        final List<Long> hiEntries = new ArrayList<>();
        hiEntries.add(0L);
        hiEntries.add(1L);
        // possible maximum due to impl. detail in DiskFPSet
        // (array index Integer.Max_Value)
        hiEntries.add((long) Integer.MAX_VALUE * 1024);
        // theoretically hiEntry can go up to Long.MAX_VALUE
        // hiEntries.add(Long.MAX_VALUE - 1l);
        // hiEntries.add(Long.MAX_VALUE);

        // loVals
        for (final Long loVal : loVals) {
            // hiVals
            for (final Long hiVal : hiVals) {
                // fps
                for (final Long fp : fps) {
                    // loEntry
                    for (final Long loEntry : loEntries) {
                        // hiEntry
                        for (final Long hiEntry : hiEntries) {
                            testCalculateMidEntry(fpSet, loVal, hiVal, fp, loEntry, hiEntry);
                        }
                    }
                }
            }
        }

        fpSet.close();
    }

    private void testCalculateMidEntry(final DiskFPSet fpSet, final long loVal, final long hiVal, final long fp, final long loEntry, final long hiEntry) {
        if (!isInvalidInput(loVal, hiVal, fp, loEntry, hiEntry)) {
            try {
                final long midEntry = fpSet.calculateMidEntry(loVal, hiVal, fp, loEntry, hiEntry);

                assertTrue(getMessage("Negative mid entry", loVal, hiVal, fp, loEntry, hiEntry, midEntry),
                        midEntry >= 0);
                assertTrue(getMessage("Not within lower bound", loVal, hiVal, fp, loEntry, hiEntry, midEntry),
                        midEntry >= loEntry);
                assertTrue(getMessage("Not within upper bound", loVal, hiVal, fp, loEntry, hiEntry, midEntry),
                        midEntry <= hiEntry);

                // DiskFPSet#diskLookup uses long addressing and thus has to multiply by 8
                assertTrue(getMessage("midEntry turned negative", loVal, hiVal, fp, loEntry, hiEntry, midEntry),
                        (midEntry * 8) >= 0);

            } catch (final RuntimeException e) {
                fail("failed to calculate for valid input (loVal, hiVal, fp, loEntry, hiEntry): " + loVal + ", "
                        + hiVal + ", " + fp + ", " + loEntry + ", " + hiEntry);
            }
        }
    }

    private String getMessage(final String txt, final long loVal, final long hiVal, final long fp, final long loEntry, final long hiEntry, final long midEntry) {
        return txt + " (loVal, hiVal, fp, loEntry, hiEntry, midEntry): " + loVal + ", "
                + hiVal + ", " + fp + ", " + loEntry + ", " + hiEntry + ", " + midEntry;
    }

    private boolean isInvalidInput(final long loVal, final long hiVal, final long fp, final long loEntry, final long hiEntry) {
        return loVal > hiVal || loVal > fp || hiVal < fp || loEntry >= hiEntry;
    }

    /**
     * Tests if {@link DiskFPSet#diskLookup(long)} returns true for a fp that is
     * first fp in first page
     * <p>
     * page size hard-coded in {@link DiskFPSet} to be 1024
     */
    @Test
    @SuppressWarnings("deprecation")
    public void testDiskLookupWithFpOnLoPage() throws Exception {
        final int freeMemory = 1000; // causes 16 in memory entries
        final FPSetConfiguration fpSetConfig = new DummyFPSetConfiguration();
        fpSetConfig.setRatio(1.0d);
        fpSetConfig.setMemory(freeMemory);
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(fpSetConfig);

        // add enough fps to cause 3 disk writes
        final long fp = 1L;
        for (long i = 0; i < 1024 * 3; i++) {
            assertFalse(fpSet.put(fp + i));
            assertTrue(fpSet.contains(fp + i));
        }

        assertTrue("Failed to lookup fp on first page", fpSet.diskLookup(fp));

        fpSet.close();
    }

    /**
     * Tests how {@link DiskFPSet#memLookup(long)} handles zeros
     */
    @Test
    public void testMemLookupWithZeros() throws Exception {
        // skip known failures which aren't likely to be fixed anytime soon
        // @see Bug #213 in general/bugzilla/index.html
        if (!runKnownFailures) {
            System.out
                    .println("Skipping test failing due to Bug #213 in general/bugzilla/index.html");
            return;
        }

        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration(.75d));
        assertFalse(fpSet.memInsert(0L));
        assertFalse(fpSet.diskLookup(0L));
        assertTrue(fpSet.memLookup(0L));

        fpSet.close();
    }

    /**
     * Tests how {@link DiskFPSet#memLookup(long)} handles Long.Min_VALUE
     */
    @Test
    public void testMemLookupWithMin() throws Exception {
        // skip known failures which aren't likely to be fixed anytime soon
        // @see Bug #213 in general/bugzilla/index.html
        if (!runKnownFailures) {
            System.out
                    .println("Skipping test failing due to Bug #213 in general/bugzilla/index.html");
            return;
        }

        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration(.75d));
        assertFalse(fpSet.memInsert(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
        assertFalse(fpSet.diskLookup(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
        assertTrue(fpSet.memLookup(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));

        fpSet.close();
    }

    /**
     * Tests how {@link DiskFPSet#memLookup(long)} handles MAx_Value
     */
    @Test
    public void testMemLookupWithMax() throws Exception {
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration(.75d));
        assertFalse(fpSet.memInsert(Long.MAX_VALUE));
        assertFalse(fpSet.diskLookup(Long.MAX_VALUE));
        assertTrue(fpSet.memLookup(Long.MAX_VALUE));

        fpSet.close();
    }

    /**
     * Tests how {@link DiskFPSet#memLookup(long)} handles zeros
     */
    @Test
    public void testDiskLookupWithZeros() throws Exception {
        final long fp = 0L;

        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration(.75d));

        // Add fp to empty fpset
        //assertFalse(fpSet.memInsert(fp));
        assertFalse(fpSet.put(fp));

        // Optionally verify that neither ram nor disk
        // contain 0L yet (before flush)
        assertFalse(fpSet.memLookup(fp));
        assertFalse(fpSet.diskLookup(fp));
        assertFalse(fpSet.contains(fp));

        // explicitly flush to disk which makes 0l "magically" appear in the set
        fpSet.flusher.flushTable();

        // mem still doesn't "see" the fp
        assertFalse(fpSet.memLookup(fp));

        // it's just on disk
        assertTrue(fpSet.diskLookup(fp));
        assertTrue(fpSet.contains(fp));

        // undefined behavior
        // assertTrue(fpSet.memLookup(fp));

        fpSet.close();
    }

    /**
     * Tests how {@link DiskFPSet#memLookup(long)} handles Long.Min_VALUE
     */
    @Test
    public void testDiskLookupWithMin() throws Exception {
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());
        assertFalse(fpSet.memInsert(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
        assertFalse(fpSet.diskLookup(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
        fpSet.flusher.flushTable();
        assertTrue(fpSet.diskLookup(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));
        // undefined behavior
        // assertTrue(fpSet.memLookup(Long.MIN_VALUE & 0x7FFFFFFFFFFFFFFFL));

        fpSet.close();
    }

    /**
     * Tests how {@link DiskFPSet#memLookup(long)} handles MAx_Value
     */
    @Test
    public void testDiskLookupWithMax() throws Exception {
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(new FPSetConfiguration());
        assertFalse(fpSet.memInsert(Long.MAX_VALUE));
        assertFalse(fpSet.diskLookup(Long.MAX_VALUE));
        fpSet.flusher.flushTable();
        assertTrue(fpSet.diskLookup(Long.MAX_VALUE));
        assertTrue(fpSet.memLookup(Long.MAX_VALUE));

        fpSet.close();
    }

    /**
     * Tests how {@link DiskFPSet#diskLookup(long)} handles max on pages
     */
    @Test
    public void testDiskLookupWithMaxOnPage() throws Exception {
        testDiskLookupOnPage(Long.MAX_VALUE);
    }

    /**
     * Tests how {@link DiskFPSet#diskLookup(long)} handles zeros on pages
     */
    @Test
    public void testDiskLookupWithZerosOnPage() throws Exception {
        // skip known failures which aren't likely to be fixed anytime soon
        // @see Bug #213 in general/bugzilla/index.html
        if (!runKnownFailures) {
            System.out
                    .println("Skipping test failing due to Bug #213 in general/bugzilla/index.html");
            return;
        }
        testDiskLookupOnPage(0L);
    }

    /**
     * Tests how {@link DiskFPSet#diskLookup(long)} handles Long#Min_Value on pages
     */
    @Test
    public void testDiskLookupWithLongMinValueOnPage() throws Exception {
        // skip known failures which aren't likely to be fixed anytime soon
        // @see Bug #213 in general/bugzilla/index.html
        if (!runKnownFailures) {
            System.out
                    .println("Skipping test failing due to Bug #213 in general/bugzilla/index.html");
            return;
        }

        testDiskLookupOnPage(Long.MIN_VALUE);
    }

    @SuppressWarnings("deprecation")
    private void testDiskLookupOnPage(final long fp) throws Exception {
        final int freeMemory = 1000; // causes 16 in memory entries
        final FPSetConfiguration fpSetConfig = new FPSetConfiguration();
        fpSetConfig.setRatio(1.0d);
        fpSetConfig.setMemory(freeMemory);
        final DiskFPSet fpSet = (DiskFPSet) getFPSet(fpSetConfig);

        // add enough fps to cause 2 disk writes
        assertFalse(fpSet.put(fp));
        for (long i = 1; i < 1024 * 2; i++) {
            assertTrue("Failed to add fingerprint", fpSet.put(fp));
            assertTrue(fpSet.contains(fp));
        }

        final long fp0 = fp & 0x7FFFFFFFFFFFFFFFL;
        assertTrue(fpSet.memLookup(fp));
        assertFalse(fpSet.diskLookup(fp0));

        fpSet.close();
    }

    /**
     * Test that both implementations - put(long) & putBlock(LongVec) - yield
     * the same results.
     */
    @Test
    public void testComparePutAndPutBlock() throws Exception {
        final FPSet putFpSet = getFPSetInitialized();
        final FPSet putBlockFpSet = getFPSetInitialized();

        final long fp = 1L;
        final LongVec fpv = new LongVec();
        fpv.add(fp);

        // put and putBlock have flipped return values %)
        final boolean putBlockRes = !putBlockFpSet.putBlock(fpv).get(0);
        assertEquals(putFpSet.put(fp), putBlockRes);

        putFpSet.close();
        putBlockFpSet.close();
    }

    /**
     * Test that both implementations - contains(long) & containsBlock(LongVec) - yield
     * the same results.
     */
    @Test
    public void testCompareContainsAndContainsBlock() throws Exception {
        final FPSet containsFpSet = getFPSetInitialized();
        final FPSet containsBlockFpSet = getFPSetInitialized();

        final long fp = 1L;
        final LongVec fpv = new LongVec();
        fpv.add(fp);

        // put and putBlock have flipped return values %)
        final boolean containsBlockRes = !containsBlockFpSet.containsBlock(fpv).get(0);
        assertEquals(containsFpSet.contains(fp), containsBlockRes);

        containsFpSet.close();
        containsBlockFpSet.close();
    }

    @Test
    public void testContainsBlock() throws Exception {
        final FPSet fpSet = getFPSetInitialized();

        final long fp = 1L;
        final LongVec fpv = new LongVec();
        fpv.add(fp);

        // BitSet is true if fp not in set
        assertTrue(fpSet.containsBlock(fpv).get(0));

        fpSet.put(fp);

        // BitSet is false if fp is in set
        assertFalse(fpSet.containsBlock(fpv).get(0));

        fpSet.close();
    }

    @Test
    public void testPutBlock() throws Exception {
        final FPSet fpSet = getFPSetInitialized();

        final long fp = 1L;
        final LongVec fpv = new LongVec();
        fpv.add(fp);

        // BitSet is true if fp not in set
        assertTrue(fpSet.putBlock(fpv).get(0));

        // BitSet is false if fp is in set
        assertFalse(fpSet.putBlock(fpv).get(0));

        fpSet.close();
    }
}
