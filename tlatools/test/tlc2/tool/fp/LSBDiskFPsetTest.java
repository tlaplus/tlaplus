// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import java.rmi.RemoteException;

public class LSBDiskFPsetTest extends AbstractHeapBasedDiskFPSetTest {
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.HeapBasedDiskFPSetTest#getDiskFPSet(tlc2.tool.fp.FPSetConfiguration)
	 */
	protected DiskFPSet getDiskFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
		return new LSBDiskFPSet(fpSetConfig);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.HeapBasedDiskFPSetTest#getLowerLimit()
	 */
	protected long getLowerLimit() {
		return 1L << 9;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractHeapBasedDiskFPSetTest#getUpperLimit()
	 */
	protected long getUpperLimit() {
		// LSBDiskFPSet uses a temporary storage array which is limited by
		// java's array length restriction. This restriction is Integer.MAX_VALUE
		return 1L << 31;
	}
}
