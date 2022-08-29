// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.fp;

import org.junit.Test;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MemFPSet;
import tlc2.util.LongVec;

import java.io.IOException;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import static org.junit.Assert.*;

public class DynamicFPSetManagerTest {

    /**
     * Test that the ctor rejects invalid values.
     */
    @Test
    public void testCtorInvalidZero() {
        try (var dfm = new DynamicFPSetManager(0)) {
        } catch (final IllegalArgumentException e) {
            return;
        }
        fail("Exception expected");
    }

    /**
     * Test that the ctor rejects invalid values.
     */
    @Test
    public void testCtorInvalidMin1() {
        try (var dfm = new DynamicFPSetManager(-1)) {

        } catch (final IllegalArgumentException e) {
            return;
        }
        fail("Exception expected");
    }

    /**
     * Test that the ctor correctly calculates its mask used to index fpset
     * servers for valid values.
     */
    @Test
    public void testCtor1() {
        try (final DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(1)) {
            final long mask = dynamicFPSetManager.getMask();
            assertEquals(1L, mask);
        }
    }

    /**
     * Test that the ctor correctly calculates its mask used to index fpset
     * servers for valid values.
     */
    @Test
    public void testCtor10() {
        try (final DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(10)) {
            final long mask = dynamicFPSetManager.getMask();
            assertEquals(15L, mask);
        }

    }

    /**
     * Test that the ctor correctly calculates its mask used to index fpset
     * servers for valid values.
     */
    @Test
    public void testCtor31() {
        try (DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(31)) {
            final long mask = dynamicFPSetManager.getMask();
            assertEquals(31L, mask);
        }
    }

    /**
     * Test that the ctor correctly calculates its mask used to index fpset
     * servers for valid values.
     */
    @Test
    public void testCtor32() {
        try (final DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(32)) {
            final long mask = dynamicFPSetManager.getMask();
            assertEquals(63L, mask);
        }
    }

    /**
     * Test that the ctor correctly calculates its mask used to index fpset
     * servers for valid values.
     */
    @Test
    public void testCtor33() {
        try (final DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(33)) {
            final long mask = dynamicFPSetManager.getMask();
            assertEquals(63L, mask);
        }
    }

    /**
     * Test that the ctor correctly calculates its mask used to index fpset
     * servers for valid values.
     */
    @Test
    public void testCtorMax() {
        try (final DynamicFPSetManager dynamicFPSetManager = new DynamicFPSetManager(Integer.MAX_VALUE)) {
            final long mask = dynamicFPSetManager.getMask();
            assertEquals((Integer.MAX_VALUE), mask);
        }
    }

    /**
     * Test that the {@link DynamicFPSetManager} correctly indexes into the
     * table of FPSet servers.
     */
    @Test
    public void testGetIndexSingleFPSet() throws Exception {
        // Simple case with a single FPSet server
        final Map<Long, Integer> pairs = new HashMap<>();
        pairs.put(Long.MAX_VALUE, 0);
        pairs.put(Long.MIN_VALUE, 0);
        pairs.put(0L, 0);
        pairs.put(1L, 0);

        doTestGetIndex(1, pairs);
    }

    /**
     * Test that the {@link DynamicFPSetManager} correctly indexes into the
     * table of FPSet servers.
     */
    @Test
    public void testGetIndex10FPSet() throws Exception {
        final Map<Long, Integer> pairs = new HashMap<>();

        pairs.put(Long.MAX_VALUE, 5);
        pairs.put(Long.MIN_VALUE, 0);

        // Test all fpsets get addressed
        pairs.put(0L, 0);
        pairs.put(1L, 1);
        pairs.put(2L, 2);
        pairs.put(3L, 3);
        pairs.put(4L, 4);
        pairs.put(5L, 5);
        pairs.put(6L, 6);
        pairs.put(7L, 7);
        pairs.put(8L, 8);
        pairs.put(9L, 9);

        // Test to correctly wrap over
        pairs.put(10L, 0);
        pairs.put(11L, 1);
        pairs.put(12L, 2);

        pairs.put(48L, 0);
        pairs.put(49L, 1);
        pairs.put(50L, 2);
        pairs.put(51L, 3);

        doTestGetIndex(10, pairs);
    }

    // Create the given amount of FPSetManagers and check if the return the integer for the given fingerprint (long)
    private void doTestGetIndex(final int expectedNumOfServers, final Map<Long, Integer> pairs) throws Exception {
        try (final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers)) {
            for (int i = 0; i < expectedNumOfServers; i++) {
                dfm.register(new MemFPSet(), "localhost" + i);
            }

            for (final Entry<Long, Integer> pair : pairs.entrySet()) {
                final long fp = pair.getKey();
                final int index = dfm.getFPSetIndex(fp);
                final int expected = pair.getValue();
                assertEquals(expected, index);
            }
        }
    }

    /**
     * Tests that reassign doesn't accept invalid values
     */
    @Test
    public void testReassingInvalidMin1() throws Exception {
        final int expectedNumOfServers = 1;
        try (final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers)) {
            for (int i = 0; i < expectedNumOfServers; i++) {
                dfm.register(new MemFPSet(), "localhost" + i);
            }

            // invalid input
            try {
                dfm.reassign(-1);
            } catch (final IllegalArgumentException e) {
                // expected
                return;
            }
            fail();
        }
    }

    /**
     * Tests that reassign doesn't accept invalid values
     */
    @Test
    public void testReassingInvalid2() throws Exception {
        final int expectedNumOfServers = 1;
        try (final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers)) {
            for (int i = 0; i < expectedNumOfServers; i++) {
                dfm.register(new MemFPSet(), "localhost" + i);
            }

            // invalid input
            try {
                dfm.reassign(expectedNumOfServers);
            } catch (final IllegalArgumentException e) {
                // expected
                return;
            }
            fail();
        }
    }

    /**
     * Tests that reassign correctly terminates with -1 when reassignment to
     * next FPSet impossible (no FPSets left)
     */
    @Test
    public void testReassingTerminate() throws Exception {
        final int expectedNumOfServers = 1;
        try (final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers)) {
            for (int i = 0; i < expectedNumOfServers; i++) {
                dfm.register(new MemFPSet(), "localhost" + i);
            }

            final int reassign = dfm.reassign(0);
            assertEquals(-1, reassign);
        }

    }

    /**
     * Tests that reassign correctly assigns to the next FPSet
     */
    @Test
    public void testReassing() throws Exception {
        final int expectedNumOfServers = 10;
        try (final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers)) {
            for (int i = 0; i < expectedNumOfServers; i++) {
                dfm.register(new MemFPSet(), "localhost" + i);
            }

            // subsequently replace all FPSets until we
            // hit the end of the list (-1)
            int reassign = dfm.reassign(1);
            assertEquals(2, reassign);

            reassign = dfm.reassign(2);
            assertEquals(3, reassign);

            reassign = dfm.reassign(3);
            assertEquals(4, reassign);

            reassign = dfm.reassign(4);
            assertEquals(5, reassign);

            reassign = dfm.reassign(5);
            assertEquals(6, reassign);

            reassign = dfm.reassign(6);
            assertEquals(7, reassign);

            reassign = dfm.reassign(7);
            assertEquals(8, reassign);

            reassign = dfm.reassign(8);
            assertEquals(9, reassign);

            reassign = dfm.reassign(9);
            assertEquals(0, reassign);

            reassign = dfm.reassign(0);
            assertEquals(-1, reassign);
        }
    }

    /**
     * Tests if the {@link FPSetManager} correctly fails over to the replacement {@link FPSet}
     */
    @Test
    public void testFailoverPut() throws Exception {
        final int expectedNumOfServers = 2;
        try (final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers)) {
            dfm.register(new FaultyFPSet(), "TestFPSet");
            dfm.register(new MemFPSet(), "RegularFPSet");

            final long fp = 2L;

            assertEquals("Assert fingerprint corresponds to TestFPSet", 0, dfm.getFPSetIndex(fp));

            // Test DFM correctly behaves first time when TestFPSet works as expected
            assertFalse(dfm.put(fp));
            assertTrue(dfm.contains(fp));

            // Test DFM correctly fails over to successor of TestFPSet
            // (Here one can observe the behavior that a fingerprint is thought to
            // be new when a FPSet crashes).
            assertFalse(dfm.put(fp));
            assertTrue(dfm.contains(fp));
        }
    }

    /**
     * Tests if the {@link FPSetManager} correctly fails over to the replacement {@link FPSet}
     */
    @Test
    public void testFailoverPutBlock() throws Exception {
        final int expectedNumOfServers = 2;

        try (final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers)) {
            dfm.register(new FaultyFPSet(), "TestFPSet");
            dfm.register(new MemFPSet(), "RegularFPSet");

            final int numOfServers = dfm.numOfServers();

            // LongVec has to have same size of IFPSetManager#numServers (putBlock
            // method contract)
            final LongVec[] fps = new LongVec[numOfServers];
            fps[0] = new LongVec();
            fps[0].add(0L);
            assertEquals("Assert fingerprint corresponds to TestFPSet", 0, dfm.getFPSetIndex(0L));
            fps[1] = new LongVec();
            fps[1].add(1L);
            assertEquals("Assert fingerprint corresponds to TestFPSet", 1, dfm.getFPSetIndex(1L));

            /* Test DFM correctly behaves first time when TestFPSet works as expected */

            BitSet[] bvs = dfm.putBlock(fps);
            assertEquals(1, bvs[0].cardinality());
            assertEquals(1, bvs[1].cardinality());

            bvs = dfm.containsBlock(fps);
            // all (the same) fingerprints are now known (meaning corresponding
            // bit in bvs[x] is zero).
            assertEquals(0, bvs[0].cardinality());
            assertEquals(0, bvs[1].cardinality());

            /*
             * Test DFM correctly fails over to successor of TestFPSet (Here one can
             * observe the behavior that a fingerprint is thought to be new when a
             * FPSet crashes).
             */

            bvs = dfm.putBlock(fps);
            assertEquals(1, bvs[0].cardinality()); // fingerprint is unknown after fpset crash
            assertEquals(0, bvs[1].cardinality());

            // The previous putBlock call has caused the FPSetManager to detect the
            // failure state of the first FPSets and reassigned the replacement FPSet.
            // Thus, it reports two alive servers
            assertEquals(1, dfm.numOfAliveServers());

            bvs = dfm.containsBlock(fps);
            assertEquals(0, bvs[0].cardinality()); // fingerprint is known again
            assertEquals(0, bvs[1].cardinality());
        }
    }

    /**
     * Tests if the {@link FPSetManager} correctly terminates if all nested FPSets fail
     */
    @Test
    public void testFailoverTerminationPutBlock() throws Exception {
        final int expectedNumOfServers = 2;

        try (final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers)) {
            dfm.register(new FaultyFPSet(), "TestFPSet1");
            dfm.register(new FaultyFPSet(), "TestFPSet2");

            final int numOfServers = dfm.numOfServers();

            // LongVec has to have same size of IFPSetManager#numServers (putBlock
            // method contract)
            final LongVec[] fps = new LongVec[numOfServers];
            fps[0] = new LongVec();
            fps[0].add(0L);
            assertEquals("Assert fingerprint corresponds to TestFPSet", 0, dfm.getFPSetIndex(0L));
            fps[1] = new LongVec();
            fps[1].add(1L);
            assertEquals("Assert fingerprint corresponds to TestFPSet", 1, dfm.getFPSetIndex(1L));

            /* Test DFM correctly behaves first time when TestFPSet works as expected */

            BitSet[] bvs = dfm.putBlock(fps);
            assertEquals(1, bvs[0].cardinality());
            assertEquals(1, bvs[1].cardinality());

            bvs = dfm.containsBlock(fps);
            // all (the same) fingerprints are now known (meaning corresponding
            // bit in bvs[x] is zero).
            assertEquals(0, bvs[0].cardinality());
            assertEquals(0, bvs[1].cardinality());

            /*
             * Test DFM correctly fails over to successor of TestFPSet (Here one can
             * observe the behavior that a fingerprint is thought to be new when a
             * FPSet crashes).
             */

            bvs = dfm.putBlock(fps);
            assertEquals(1, bvs[0].cardinality()); // fingerprint is unknown after fpset crash
            assertEquals(1, bvs[1].cardinality());

            // The previous putBlock call has caused the FPSetManager to detect the
            // failure state of both FPSets
            assertEquals(0, dfm.numOfAliveServers());

            bvs = dfm.containsBlock(fps);
            assertEquals(1, bvs[0].cardinality()); // fingerprint is known again
            assertEquals(1, bvs[1].cardinality());
        }
    }

    /**
     * Tests if the {@link FPSetManager} correctly terminates if all nested FPSets fail
     */
    @Test
    public void testFailoverTerminationPutBlockConcurrent() throws Exception {
        final int expectedNumOfServers = 2;

        try (final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers)) {
            dfm.register(new FaultyFPSet(), "TestFPSet1");
            dfm.register(new FaultyFPSet(), "TestFPSet2");

            final int numOfServers = dfm.numOfServers();


            // LongVec has to have same size of IFPSetManager#numServers (putBlock
            // method contract)
            final LongVec[] fps = new LongVec[numOfServers];
            fps[0] = new LongVec();
            fps[0].add(0L);
            assertEquals("Assert fingerprint corresponds to TestFPSet", 0, dfm.getFPSetIndex(0L));
            fps[1] = new LongVec();
            fps[1].add(1L);
            assertEquals("Assert fingerprint corresponds to TestFPSet", 1, dfm.getFPSetIndex(1L));

            /* Test DFM correctly behaves first time when TestFPSet works as expected */
            final ExecutorService es = Executors.newCachedThreadPool();
            try {
                BitSet[] bvs = dfm.putBlock(fps, es);
                assertEquals(1, bvs[0].cardinality());
                assertEquals(1, bvs[1].cardinality());

                bvs = dfm.containsBlock(fps, es);
                // all (the same) fingerprints are now known (meaning corresponding
                // bit in bvs[x] is zero).
                assertEquals(0, bvs[0].cardinality());
                assertEquals(0, bvs[1].cardinality());

                /*
                 * Test DFM correctly fails over to successor of TestFPSet (Here one can
                 * observe the behavior that a fingerprint is thought to be new when a
                 * FPSet crashes).
                 */

                bvs = dfm.putBlock(fps, es);
                assertEquals(1, bvs[0].cardinality()); // fingerprint is unknown after fpset crash
                assertEquals(1, bvs[1].cardinality());

                // The previous putBlock call has caused the FPSetManager to detect the
                // failure state of both FPSets
                assertEquals(0, dfm.numOfAliveServers());

                bvs = dfm.containsBlock(fps, es);
                assertEquals(1, bvs[0].cardinality()); // fingerprint is known again
                assertEquals(1, bvs[1].cardinality());
            } finally {
                es.shutdown();
            }
        }
    }

    /**
     * Tests if the {@link FPSetManager} returns the BitSet[] with correct
     * order.
     * <p>
     * Due to the nature of concurrency, this test can pass by chance (inversely
     * proportional probability to expectedNumOfServers). However, repeatedly
     * test execution is expected to fail most of the time if
     * {@link DynamicFPSetManager} is indeed faulty (pay attention to
     * intermittent test failures).
     */
    @Test
    public void testPutBlockConcurrentOrder() throws IOException {
        final int expectedNumOfServers = 20;

        try (final DynamicFPSetManager dfm = new DynamicFPSetManager(expectedNumOfServers)) {

            // expectedNumOfServers - 1 empty fpsets
            for (int i = 0; i < expectedNumOfServers - 1; i++) {
                dfm.register(new MemFPSet(), "TestFPSet" + i);
            }

            final long fp = 1L;

            // add a single non-empty fpset at the last position
            final FPSet nonEmptyFPSet = new MemFPSet();
            nonEmptyFPSet.put(fp);
            dfm.register(nonEmptyFPSet, "localhost");


            final LongVec[] fps = new LongVec[expectedNumOfServers];
            for (int i = 0; i < expectedNumOfServers; i++) {
                fps[i] = new LongVec();
                fps[i].add(fp);
            }

            // Check if the last element in the resulting bitvector has the bit for the fp set
            final ExecutorService es = Executors.newCachedThreadPool();
            try {
                final BitSet[] bvs = dfm.containsBlock(fps, es);
                // The first expectedNumOfServers - 1 must not contain the fp
                for (int i = 0; i < expectedNumOfServers - 1; i++) {
                    assertEquals(1, bvs[i].cardinality());
                }

                // The last element is expected to contain the fingerprint
                assertEquals(0, bvs[expectedNumOfServers - 1].cardinality());
            } finally {
                es.shutdown();
            }
        }
    }
}
