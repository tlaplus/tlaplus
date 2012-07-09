// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.IOException;

public class MSBDiskFPSetTest extends FPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(long)
	 */
	@Override
	protected FPSet getFPSet(long freeMemoryInBytes) throws IOException {
		return new MSBDiskFPSet(freeMemoryInBytes / (long) DiskFPSet.LongSize);
	}

}
