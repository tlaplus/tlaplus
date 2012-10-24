// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.rmi.RemoteException;

import junit.framework.TestCase;

public abstract class AbstractHeapBasedDiskFPSetTest extends TestCase {
	
	/* Test the lower limits */
	
	public void testCtorLLMinus1() throws RemoteException {
		doTest(getLowerLimit() - 1);
	}
	
	public void testCtorLL() throws RemoteException {
		doTest(getLowerLimit());
	}

	public void testCtorLLPlus1() throws RemoteException {
		doTest(getLowerLimit() + 1);
	}
	
	public void testCtorLLNextPow2Min1() throws RemoteException {
		doTest((getLowerLimit() << 1) - 1);
	}
	
	/* Test with a power far away from upper/lower limits */
	
	public void testCtorPow16Minus1() throws RemoteException {
		doTest((1L << 16) - 1);
	}
	
	public void testCtorPow16() throws RemoteException {
		doTest(1L << 16);
	}

	public void testCtorPow16Plus1() throws RemoteException {
		doTest((1L << 16) + 1);
	}
	
	public void testCtorPow16NextPow2Min1() throws RemoteException {
		doTest(((1L << 16) << 1) - 1);
	}
	
	/* Test the upper limits */
	
	public void testCtorULMinus1() throws RemoteException {
		doTest(getUpperLimit() - 1);
	}
	
	public void testCtorUL() throws RemoteException {
		doTest(getUpperLimit());
	}

	public void testCtorULPlus1() throws RemoteException {
		doTest(getUpperLimit() + 1);
	}
	
	public void testCtorULNextPow2Min1() throws RemoteException {
		doTest((getUpperLimit() << 1) - 1);
	}
	
	/* Helper */

	@SuppressWarnings("deprecation")
	protected void doTest(final long physicalMemoryInBytes) throws RemoteException {
		final FPSetConfiguration fpSetConfig = new DummyFPSetConfiguration();
		fpSetConfig.setMemory(physicalMemoryInBytes);
		
		final DiskFPSet fpset = getDiskFPSet(fpSetConfig);
		long maxTblCntInBytes = fpset.getMaxTblCnt() * FPSet.LongSize; // Convert from logical to physical
		
		// Always allocate less storage than given 
		assertTrue("Internal storage exceeds allocated memory", physicalMemoryInBytes >= maxTblCntInBytes);
		
		// Storage with zero space for a fingerprint does make much sense, does it?
		assertTrue("Internal storage underflow allocated memory", 0L < maxTblCntInBytes);
		
		// We happen to know that LSBDiskFPSet reserves some memory to auxiliary
		// storage. Make this reservation the lower bound for the primary
		// storage. We div by 2 to account for the fact that both
		// implementations round down to the next power of 2.
		double lowerLimit = (physicalMemoryInBytes / 2) / fpset.getAuxiliaryStorageRequirement();
		assertTrue("Internal storage falls short lower allocation limit", lowerLimit <= maxTblCntInBytes);
	}

	protected abstract DiskFPSet getDiskFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException;

	/**
	 * @return The lower size limit the {@link HeapBasedDiskFPSet} can handle.
	 *         It is determined by the implementation's
	 *         {@link DiskFPSet#getAuxiliaryStorageRequirement()}.
	 */
	protected abstract long getLowerLimit();

	/**
	 * @return The upper size limit the {@link HeapBasedDiskFPSet} can handle.
	 */
	protected abstract long getUpperLimit();
}
