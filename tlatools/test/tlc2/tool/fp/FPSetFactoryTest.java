// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.rmi.NoSuchObjectException;
import java.rmi.RemoteException;
import org.junit.Test;

import tlc2.tool.distributed.fp.FPSetRMI;

@SuppressWarnings("deprecation")
public class FPSetFactoryTest {
	// Has to be larger than util.TLCRuntime.MinFpMemSize. For off-heap/non-heap
	// tests it should not exceed what the VM allocates by default (usually
	// 64mb). 64mb is also the default used by util.TLCRuntime.getNonHeapPhysicalMemory().
	private static final long MEMORY = 64L * 1024L * 1024L;

	/* Test diskfpset subclasses which always require two instances */
	
	@Test
	public void testGetDiskFPSet() {
		assertTrue(FPSetFactory.isDiskFPSet(DiskFPSet.class.getName()));
		assertTrue(FPSetFactory.isDiskFPSet(HeapBasedDiskFPSet.class.getName()));
		assertTrue(FPSetFactory.isDiskFPSet(OffHeapDiskFPSet.class.getName()));
		assertTrue(FPSetFactory.isDiskFPSet(LSBDiskFPSet.class.getName()));
		assertTrue(FPSetFactory.isDiskFPSet(MSBDiskFPSet.class.getName()));

		assertFalse(FPSetFactory.isDiskFPSet(FPSet.class.getName()));
		assertFalse(FPSetFactory.isDiskFPSet(FPSetRMI.class.getName()));
		
		assertFalse(FPSetFactory.isDiskFPSet(MultiFPSet.class.getName()));
		
		assertFalse(FPSetFactory.isDiskFPSet(MemFPSet.class.getName()));
		assertFalse(FPSetFactory.isDiskFPSet(MemFPSet1.class.getName()));
		assertFalse(FPSetFactory.isDiskFPSet(MemFPSet2.class.getName()));
		
		System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		assertTrue(fpSetConfiguration.allowsNesting());
	}
	
	/* Test single FPSet with default memory */

	@Test
	public void testGetFPSetMSB() throws RemoteException {
		// Explicitly set MSBDiskFPSet to overwrite any previous setting (if any)
		System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		doTestGetFPSet(MSBDiskFPSet.class, fpSetConfiguration);
	}

	@Test
	public void testGetFPSetLSB() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		doTestGetFPSet(LSBDiskFPSet.class, fpSetConfiguration);
	}

	@Test
	public void testGetFPSetOffHeap() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		doTestGetFPSet(OffHeapDiskFPSet.class, fpSetConfiguration);
	}

	/* Test single FPSet with explicit memory */
	
	@Test
	public void testGetFPSetMSBWithMem() throws RemoteException {
		// Explicitly set MSBDiskFPSet to overwrite any previous setting (if any)
		System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(1.0d);
		FPSet fpSet = doTestGetFPSet(MSBDiskFPSet.class, fpSetConfiguration);
		assertEquals(MEMORY, fpSet.getConfiguration().getMemoryInBytes());

		doTestNested(MSBDiskFPSet.class, fpSetConfiguration, (MultiFPSet) fpSet);
	}

	@Test
	public void testGetFPSetLSBWithMem() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(1.0d);
		FPSet fpSet = doTestGetFPSet(LSBDiskFPSet.class, fpSetConfiguration);
		assertEquals(MEMORY, fpSet.getConfiguration().getMemoryInBytes());

		doTestNested(LSBDiskFPSet.class, fpSetConfiguration, (MultiFPSet) fpSet);
	}

	@Test
	public void testGetFPSetOffHeapWithMem() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(1.0d);
		FPSet fpSet = doTestGetFPSet(OffHeapDiskFPSet.class, fpSetConfiguration);
		assertEquals(MEMORY, fpSet.getConfiguration().getMemoryInBytes());

		doTestNested(OffHeapDiskFPSet.class, fpSetConfiguration, (MultiFPSet) fpSet);
	}
	
	/* Test single FPSet with explicit memory and ratio */
	
	@Test
	public void testGetFPSetMSBWithMemAndRatio() throws RemoteException {
		// Explicitly set MSBDiskFPSet to overwrite any previous setting (if any)
		System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(.5d);
		FPSet fpSet = doTestGetFPSet(MSBDiskFPSet.class, fpSetConfiguration);
		assertEquals(MEMORY / 2, fpSet.getConfiguration().getMemoryInBytes());

		doTestNested(MSBDiskFPSet.class, fpSetConfiguration, (MultiFPSet) fpSet);
	}

	@Test
	public void testGetFPSetLSBWithMemAndRatio() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(.5d);
		FPSet fpSet = doTestGetFPSet(LSBDiskFPSet.class, fpSetConfiguration);
		assertEquals(MEMORY / 2, fpSet.getConfiguration().getMemoryInBytes());


		doTestNested(LSBDiskFPSet.class, fpSetConfiguration, (MultiFPSet) fpSet);
	}

	@Test
	public void testGetFPSetOffHeapWithMemAndRatio() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setRatio(.5d);
		FPSet fpSet = doTestGetFPSet(OffHeapDiskFPSet.class, fpSetConfiguration);
		
		// Offheap allocates all 100% of memory as it's the only consumer of
		// non-heap memory
		assertEquals(MEMORY, fpSet.getConfiguration().getMemoryInBytes());

		doTestNested(OffHeapDiskFPSet.class, fpSetConfiguration, (MultiFPSet) fpSet);
	}
	
	/* Test MultiFPSet with default memory */
	
	@Test
	public void testGetFPSetMultiFPSet() throws RemoteException {
		// Explicitly set MSBDiskFPSet to overwrite any previous setting (if any)
		System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setFpBits(1);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MultiFPSet.class, fpSetConfiguration);
		
		doTestNested(MSBDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	@Test
	public void testGetFPSetLSBMultiFPSet() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setFpBits(1);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MultiFPSet.class, fpSetConfiguration);

		doTestNested(LSBDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	@Test
	public void testGetFPSetOffHeapMultiFPSet() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setFpBits(1);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MultiFPSet.class, fpSetConfiguration);

		doTestNested(OffHeapDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	/* Test MultiFPSet with explicit memory */

	@Test
	public void testGetFPSetMultiFPSetWithMem() throws RemoteException {
		// Explicitly set MSBDiskFPSet to overwrite any previous setting (if any)
		System.setProperty(FPSetFactory.IMPL_PROPERTY, MSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setFpBits(1);
		fpSetConfiguration.setRatio(1.0d);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MultiFPSet.class, fpSetConfiguration);
		
		doTestNested(MSBDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	@Test
	public void testGetFPSetLSBMultiFPSetWithMem() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, LSBDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setFpBits(1);
		fpSetConfiguration.setRatio(1.0d);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MultiFPSet.class, fpSetConfiguration);

		doTestNested(LSBDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	@Test
	public void testGetFPSetOffHeapMultiFPSetWithMem() throws RemoteException {
		System.setProperty(FPSetFactory.IMPL_PROPERTY, OffHeapDiskFPSet.class.getName());
		final FPSetConfiguration fpSetConfiguration = new FPSetConfiguration();
		fpSetConfiguration.setMemory(MEMORY);
		fpSetConfiguration.setFpBits(1);
		fpSetConfiguration.setRatio(1.0d);
		final MultiFPSet mFPSet = (MultiFPSet) doTestGetFPSet(MultiFPSet.class, fpSetConfiguration);

		doTestNested(OffHeapDiskFPSet.class, fpSetConfiguration, mFPSet);
	}
	
	/* Helper methods */
	
	private FPSet doTestGetFPSet(final Class<? extends FPSet> class1, final FPSetConfiguration fpSetConfig) throws RemoteException, NoSuchObjectException {
		final FPSet fpSet = FPSetFactory.getFPSet(fpSetConfig);
		if (!FPSetFactory.isDiskFPSet(class1.getName())) {
			assertTrue(class1.isAssignableFrom(fpSet.getClass()));
		}
		
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
