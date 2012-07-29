// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.IOException;

import util.TLCRuntime;

public class OffHeapDiskFPSetTest extends FPSetTest {
	
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

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(long)
	 */
	@Override
	protected FPSet getFPSet(long freeMemoryInBytes) throws IOException {
		long freeMemoryInFPs = TLCRuntime.getInstance().getNonHeapPhysicalMemory() / 8L;
		return new OffHeapDiskFPSet(freeMemoryInFPs);
	}
}
