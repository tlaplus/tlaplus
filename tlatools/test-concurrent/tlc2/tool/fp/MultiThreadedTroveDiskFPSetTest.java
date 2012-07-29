// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.IOException;

import util.TLCRuntime;

public class MultiThreadedTroveDiskFPSetTest extends MultiThreadedFPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(long)
	 */
	@Override
	protected FPSet getFPSet(long freeMemoryInBytes) throws IOException {
		long freeMemoryInFPs = TLCRuntime.getInstance().getNonHeapPhysicalMemory() / (long) DiskFPSet.LongSize;
		return new TroveOffHeapDiskFPSet(freeMemoryInFPs);
	}
}
