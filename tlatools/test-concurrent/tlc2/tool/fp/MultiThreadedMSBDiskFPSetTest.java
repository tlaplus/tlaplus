// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.IOException;

import tlc2.tool.fp.DiskFPSet;
import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MSBDiskFPSet;

public class MultiThreadedMSBDiskFPSetTest extends MultiThreadedFPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(long)
	 */
	@Override
	protected FPSet getFPSet(long freeMemoryInBytes) throws IOException {
		long maxInMemoryCapacity = freeMemoryInBytes / (long) FPSet.LongSize;
		return new MSBDiskFPSet(maxInMemoryCapacity);
	}
}
