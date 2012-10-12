// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.IOException;

import util.TLCRuntime;

public class MultiThreadedOffHeapDiskFPSetTest extends MultiThreadedFPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(long)
	 */
	@Override
	protected FPSet getFPSet(final FPSetConfiguration fpSetConfig) throws IOException {
		return new OffHeapDiskFPSet(new FPSetConfiguration(TLCRuntime
				.getInstance().getNonHeapPhysicalMemory()));
	}
}
