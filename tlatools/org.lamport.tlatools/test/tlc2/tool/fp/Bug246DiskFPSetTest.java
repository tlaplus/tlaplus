// Copyright (c) Jan 9, 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import org.junit.Test;
import util.TLCRuntime;

import static org.junit.Assert.*;

/**
 * @author Markus Alexander Kuppe
 */
public class Bug246DiskFPSetTest {

    /**
     * Tests if the DiskFPSet gets correctly flushed to disk (if the fp spaces is unevenly distributed) or causes an {@link OutOfMemoryError}
     */
    @Test
    @SuppressWarnings("deprecation")
    public void testLinearFillup() throws Exception {
        final long vmMaxMemory = Runtime.getRuntime().maxMemory();
        final long maxMemoryInBytes = TLCRuntime.getInstance().getFPMemSize(0.5d);
        assertTrue("Not enough memory dedicated to JVM, increase -Vmx value", vmMaxMemory > maxMemoryInBytes);

        //TODO maxMemoryInBytes actually max amount of fingerprints which technically fit into memory?
        final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
        fpSetConfiguration.setMemory(maxMemoryInBytes);
        fpSetConfiguration.setRatio(1.0d);

        long bucketCapacity = 0;

        long tblCapacity = 0;
        long tblLoad = 0;
        long tblCnt = 0;

        int growDiskMark = 0;

        try (DummyDiskFPSet fpSet = new DummyDiskFPSet(fpSetConfiguration)) {
            fpSet.init(0, System.getProperty("java.io.tmpdir"), getClass().getName() + System.currentTimeMillis());

            // Linearly fill DiskFPSet in-memory storage to simulate an unevenly distributed fp space
            for (int i = 0; i < fpSet.getTblCapacity() - 1; i++) {
                // since n least significant bits are used for tbl addressing,
                // make sure to add values that cause buckets to be filled up
                // too. This is the case, if values start with Long.MAX_VALUE and decrease by one.
                final long fp = Long.MAX_VALUE - i;

                // make sure not to add duplicates
                assertFalse("Unexpected duplicated: " + fp, fpSet.put(fp));
                bucketCapacity = fpSet.getBucketCapacity();

                tblLoad = fpSet.getTblLoad();
                tblCapacity = fpSet.getTblCapacity();
                tblCnt = fpSet.getTblCnt();

                growDiskMark = fpSet.getGrowDiskMark();
            }
        } catch (final OutOfMemoryError e) {
            // null fpSet and run a System.gc() to reclaim its allocated memory.
            // Afterwards we hope to gracefully report test outcome.
            System.gc();

            assertEquals("Expect not to have flushed to disk", 0, growDiskMark);

            // stats

            String buf = "Bucket Capacity: " + bucketCapacity +
                    "Tbl Capacity: " + tblCapacity +
                    "Tbl Load: " + tblLoad +
                    "Tbl Cnt: " + tblCnt;


            fail("OOM occurred (not flush to disk) " + buf);
        }
    }

    @Test
    public void testFlushDiskFPSet() {

//		// Dedicate 90% of VM memory to DiskFPSet 
//		final long vmMaxMemory = Runtime.getRuntime().maxMemory();
//		long maxMemoryInBytes = TLCRuntime.getInstance().getFPMemSize(0.5d);
//		assertTrue("Not enough memory dedicated to JVM, increase -Vmx value", vmMaxMemory > maxMemoryInBytes);
//		
//		final DummyDiskFPSet fpSet = new DummyDiskFPSet(maxMemoryInBytes);
//		fpSet.init(0, System.getProperty("java.io.tmpdir"), getClass().getName()+System.currentTimeMillis());
//
//		long slotCount = fpSet.getAllocatedSlotCnt();
//		
//		final int capacity = fpSet.getTblCapacity();
////		assertTrue((capacity * DiskFPSet.InitialBucketCapacity));
//		
//		// Fill DiskFPSet in-memory storage so a disk-flush becomes necessary 
//		for(int i =  0; i < capacity - 1; i++) {
//			// make sure not to add duplicates
//			assertFalse("Unexpected duplicated: " + i, fpSet.put(i));
//		}
//		
//		// flush table which must not cause a OOM exception
//		try {
//			fpSet.flushTable();
//		} catch (OutOfMemoryError e) {
//			fail(e.getMessage());
//		}
//		finally {
//			fpSet.close();
//		}
    }
}
