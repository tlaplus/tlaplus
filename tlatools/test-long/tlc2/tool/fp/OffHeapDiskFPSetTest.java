// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.IOException;
import java.util.Random;

import util.TLCRuntime;

public class OffHeapDiskFPSetTest extends FPSetTest {
	
	private static final int FLUSHES = 4;

	public void testCollisionBucket() throws IOException {
		long freeMemory = getFreeMemoryInBytes();
		final FPSet fpSet = getFPSet(freeMemory);
		fpSet.init(1, tmpdir, filename);

		for (int i = 0; i < DiskFPSet.InitialBucketCapacity + 1; i++) {
			assertFalse(fpSet.put(i+1L));
			assertTrue(fpSet.contains(i+1L));
		}
	}

	public void testPosition() throws IOException {
		long freeMemory = getFreeMemoryInBytes();
		final FPSet fpSet = getFPSet(freeMemory);
		fpSet.init(1, tmpdir, filename);

		// max expected to cause highest position
		assertFalse(fpSet.put(Long.MAX_VALUE));
		assertTrue(fpSet.contains(Long.MAX_VALUE));
		
		// min expected to cause lowest position
		assertFalse(fpSet.put(1L));
		assertTrue(fpSet.contains(1L));
	}
	
	/**
	 * 
	 */
	public void testMultipleFlushes() throws IOException {
		final FPSet fpSet = getFPSet(-1L);
		fpSet.init(1, tmpdir, filename);
		
		final Random rnd = new Random(RNG_SEED);
		
		// Divide the allocated memory to approximate how many fingerprints will
		// have to inserted into the fpset before it starts flushing to disk.
		long freeMemoryInFPs = TLCRuntime.getInstance()
				.getNonHeapPhysicalMemory() / (long) FPSet.LongSize;

		// For n flushes, insert freeMemoryInFPs into the fp and check the
		// invariant afterwards.
		for (int flushes = 0; flushes < FLUSHES; flushes++) {
			for (long i = 1; i < freeMemoryInFPs; i++) {
				assertFalse(fpSet.put(rnd.nextLong()));
			}
			fpSet.checkInvariant(freeMemoryInFPs);
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(long)
	 */
	@Override
	protected FPSet getFPSet(long freeMemoryInBytes) throws IOException {
		long freeMemoryInFPs = TLCRuntime.getInstance().getNonHeapPhysicalMemory() / (long) FPSet.LongSize;
		return new OffHeapDiskFPSet(freeMemoryInFPs);
	}
}
