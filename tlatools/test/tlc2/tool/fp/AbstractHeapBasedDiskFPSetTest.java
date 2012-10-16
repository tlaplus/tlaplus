// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import java.rmi.RemoteException;

import junit.framework.TestCase;

public abstract class AbstractHeapBasedDiskFPSetTest extends TestCase {
	
	/* Test the lower limits */
	
	public void testCtorLLMinus1() throws RemoteException {
		final long physicalMemory = getLowerLimit() - 1; // in bytes
		doTest(physicalMemory);
	}
	
	public void testCtorLL() throws RemoteException {
		final long physicalMemory = getLowerLimit(); // in bytes
		doTest(physicalMemory);
	}

	public void testCtorLLPlus1() throws RemoteException {
		final long physicalMemory = getLowerLimit() + 1; // in bytes
		doTest(physicalMemory);
	}
	
	/* Test with a power far away from upper/lower limits */
	
	public void testCtorPow16Minus1() throws RemoteException {
		final long physicalMemory = (1L << 16) - 1; // in bytes
		doTest(physicalMemory);
	}
	
	public void testCtorPow16() throws RemoteException {
		final long physicalMemory = 1L << 16; // in bytes
		doTest(physicalMemory);
	}

	public void testCtorPow16Plus1() throws RemoteException {
		final long physicalMemory = (1L << 16) + 1; // in bytes
		doTest(physicalMemory);
	}
	
	/* Helper */

	@SuppressWarnings("deprecation")
	protected void doTest(final long physicalMemoryInBytes) throws RemoteException {
		final FPSetConfiguration fpSetConfig = new DummyFPSetConfiguration();
		fpSetConfig.setMemory(physicalMemoryInBytes);
		
		final DiskFPSet fpset = getDiskFPSet(fpSetConfig);
		long maxTblCnt = fpset.getMaxTblCnt() * FPSet.LongSize; // Convert from logical to physical
		
		// Always allocate less storage than given 
		assertTrue("Internal storage exceeds allocated memory", physicalMemoryInBytes >= maxTblCnt);
		
		// Storage with zero space for a fingerprint does make much sense, does it?
		assertTrue("Internal storage underflow allocated memory", 0L < maxTblCnt * FPSet.LongSize);
		
		// We happen to know that LSBDiskFPSet reserves some memory to auxiliary
		// storage. Make this reservation the lower bound for the primary
		// storage.
		double lowerLimit = (physicalMemoryInBytes / 2) / fpset.getAuxiliaryStorageRequirement();
		assertTrue("Internal storage exceeds lower allocation limit", lowerLimit <= maxTblCnt);
	}

	protected abstract DiskFPSet getDiskFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException;

	/**
	 * @return The lower size limit the {@link HeapBasedDiskFPSet} can handle.
	 *         It is determined by the implementation's
	 *         {@link DiskFPSet#getAuxiliaryStorageRequirement()}.
	 */
	protected abstract long getLowerLimit();
}
