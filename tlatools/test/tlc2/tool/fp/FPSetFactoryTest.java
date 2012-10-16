// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import java.rmi.NoSuchObjectException;
import java.rmi.RemoteException;

import junit.framework.TestCase;

@SuppressWarnings("deprecation")
public class FPSetFactoryTest extends TestCase {
	// Has to be larger than util.TLCRuntime.MinFpMemSize. For off-heap/non-heap
	// tests it should not exceed what the VM allocates by default (usually
	// 64mb). 64mb is also the default used by util.TLCRuntime.getNonHeapPhysicalMemory().
	private static final long MEMORY = 64L * 1024L * 1024L;

	/* Test single FPSet with default memory */

	public void testGetFPSetMSB() throws RemoteException {
		// Explicitly set MSBDiskFPSet to overwrite any previous setting (if any)
		System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		doTestGetFPSet(MSBDiskFPSet.class, fpSetConfiguration);
	}

	public void testGetFPSetLSB() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		doTestGetFPSet(LSBDiskFPSet.class, fpSetConfiguration);
	}

	public void testGetFPSetOffHeap() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		doTestGetFPSet(OffHeapDiskFPSet.class, fpSetConfiguration);
	}

	/* Test single FPSet with explicit memory */
	
	public void testGetFPSetMSBWithMem() throws RemoteException {
		// Explicitly set MSBDiskFPSet to overwrite any previous setting (if any)
		System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(1.0d);
		FPSet fpSet = doTestGetFPSet(MSBDiskFPSet.class, fpSetConfiguration);
		assertEquals(MEMORY, fpSet.getConfiguration().getMemoryInBytes());
		
		// non-multifpsets can be cast to diskfpsets to expose statistics
		// interface
		final DiskFPSet diskFPSet = (DiskFPSet) fpSet;
		assertTrue((MEMORY / FPSet.LongSize) > diskFPSet.getMaxTblCnt());
	}

	public void testGetFPSetLSBWithMem() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(1.0d);
		FPSet fpSet = doTestGetFPSet(LSBDiskFPSet.class, fpSetConfiguration);
		assertEquals(MEMORY, fpSet.getConfiguration().getMemoryInBytes());

		// non-multifpsets can be cast to diskfpsets to expose statistics
		// interface
		final DiskFPSet diskFPSet = (DiskFPSet) fpSet;
		// LSB implementation can only allocate half of its memory for primary
		// fingerprint storage (see auxiliary storage)
		assertTrue(((MEMORY / FPSet.LongSize) / 2) > diskFPSet.getMaxTblCnt());
	}

	public void testGetFPSetOffHeapWithMem() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(1.0d);
		FPSet fpSet = doTestGetFPSet(OffHeapDiskFPSet.class, fpSetConfiguration);
		assertEquals(MEMORY, fpSet.getConfiguration().getMemoryInBytes());

		// non-multifpsets can be cast to diskfpsets to expose statistics
		// interface
		final DiskFPSet diskFPSet = (DiskFPSet) fpSet;
		assertEquals((MEMORY / FPSet.LongSize), diskFPSet.getMaxTblCnt());
	}
	
	/* Test single FPSet with explicit memory and ratio */
	
	public void testGetFPSetMSBWithMemAndRatio() throws RemoteException {
		// Explicitly set MSBDiskFPSet to overwrite any previous setting (if any)
		System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(.5d);
		FPSet fpSet = doTestGetFPSet(MSBDiskFPSet.class, fpSetConfiguration);
		assertEquals(MEMORY / 2, fpSet.getConfiguration().getMemoryInBytes());
		
		// non-multifpsets can be cast to diskfpsets to expose statistics
		// interface
		final DiskFPSet diskFPSet = (DiskFPSet) fpSet;
		assertTrue((MEMORY / FPSet.LongSize) > diskFPSet.getMaxTblCnt());
	}

	public void testGetFPSetLSBWithMemAndRatio() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(.5d);
		FPSet fpSet = doTestGetFPSet(LSBDiskFPSet.class, fpSetConfiguration);
		assertEquals(MEMORY / 2, fpSet.getConfiguration().getMemoryInBytes());

		// non-multifpsets can be cast to diskfpsets to expose statistics
		// interface
		final DiskFPSet diskFPSet = (DiskFPSet) fpSet;
		// LSB implementation can only allocate half of its memory for primary
		// fingerprint storage (see auxiliary storage)
		assertTrue((MEMORY / FPSet.LongSize) > diskFPSet.getMaxTblCnt());
	}

	public void testGetFPSetOffHeapWithMemAndRatio() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(.5d);
		FPSet fpSet = doTestGetFPSet(OffHeapDiskFPSet.class, fpSetConfiguration);
		
		// Offheap allocates all 100% of memory as it's the only consumer of
		// non-heap memory
		assertEquals(MEMORY, fpSet.getConfiguration().getMemoryInBytes());

		// non-multifpsets can be cast to diskfpsets to expose statistics
		// interface
		final DiskFPSet diskFPSet = (DiskFPSet) fpSet;
		assertEquals((MEMORY / FPSet.LongSize), diskFPSet.getMaxTblCnt());
	}
	
	/* Test MultiFPSet with default memory */
	
	public void testGetFPSetMultiFPSet() throws RemoteException {
		// Explicitly set MSBDiskFPSet to overwrite any previous setting (if any)
		System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setFpBits(1);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MSBMultiFPSet.class, fpSetConfiguration);
		
		doTestNested(MSBDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	public void testGetFPSetLSBMultiFPSet() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setFpBits(1);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MultiFPSet.class, fpSetConfiguration);

		doTestNested(LSBDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	public void testGetFPSetOffHeapMultiFPSet() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setFpBits(1);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MSBMultiFPSet.class, fpSetConfiguration);

		doTestNested(OffHeapDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	/* Test MultiFPSet with explicit memory */

	public void testGetFPSetMultiFPSetWithMem() throws RemoteException {
		// Explicitly set MSBDiskFPSet to overwrite any previous setting (if any)
		System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setFpBits(1);
		fpSetConfiguration.setRatio(1.0d);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MSBMultiFPSet.class, fpSetConfiguration);
		
		doTestNested(MSBDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	public void testGetFPSetLSBMultiFPSetWithMem() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setFpBits(1);
		fpSetConfiguration.setRatio(1.0d);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MultiFPSet.class, fpSetConfiguration);

		doTestNested(LSBDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	public void testGetFPSetOffHeapMultiFPSetWithMem() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setFpBits(1);
		fpSetConfiguration.setRatio(1.0d);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MSBMultiFPSet.class, fpSetConfiguration);

		doTestNested(OffHeapDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	/* Helper methods */
	
	private FPSet doTestGetFPSet(final Class<? extends FPSet> class1, final FPSetConfiguration fpSetConfig) throws RemoteException, NoSuchObjectException {
		final FPSet fpSet = FPSetFactory.getFPSet(fpSetConfig);
		assertTrue(class1.isAssignableFrom(fpSet.getClass()));
		
		return fpSet;
	}
	
	private void doTestNested(final Class<? extends FPSet> clazz, final FPSetConfiguration fpSetConfiguration,
			final MultiFPSet mFPSet) {
		final FPSet[] fpSets = mFPSet.getFPSets();

		// Check expected amount of fpSets created
		assertEquals(fpSetConfiguration.getMultiFPSetCnt(), fpSets.length);
		
		long memoryInBytes = 0L;
		for (FPSet fpSet : fpSets) {
			// Check if all nested FPSets have proper type
			assertTrue(clazz.isAssignableFrom(fpSet.getClass()));
			
			// Check if correct amount of memory allocated/dedicated
			memoryInBytes += fpSet.getConfiguration().getMemoryInBytes();
			
			// Check correct memory again (this time via DiskFPSet stats)
			if (fpSet instanceof FPSetStatistic) {
				long maxTblCnt = ((FPSetStatistic) fpSet).getMaxTblCnt();
				// make sure nested FPSets don't overallocate memory
				assertTrue("Nested FPSet has over-allocated memory.", fpSet.getConfiguration()
						.getMemoryInFingerprintCnt() >= maxTblCnt);
				
				assertTrue(fpSet.getConfiguration().getMemoryInFingerprintCnt() >= maxTblCnt);
			}
		}
		
		// All nested FPSets combined are supposed to use all FPSet memory
		// dedicated to the MultiFPSet (unless the user decides to live with the
		// implementation default)
		assertEquals(mFPSet.getConfiguration().getMemoryInBytes(), memoryInBytes);
	}
}
