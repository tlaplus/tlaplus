// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.IOException;
import java.rmi.RemoteException;
import java.util.NoSuchElementException;

import tlc2.tool.fp.MSBDiskFPSet.TLCIterator;

public class MSBDiskFPSetTest2 extends AbstractHeapBasedDiskFPSetTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.HeapBasedDiskFPSetTest#getDiskFPSet(tlc2.tool.fp.FPSetConfiguration)
	 */
	protected DiskFPSet getDiskFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
		return new MSBDiskFPSet(fpSetConfig);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.HeapBasedDiskFPSetTest#getLowerLimit()
	 */
	protected long getLowerLimit() {
		return 1L << 8;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractHeapBasedDiskFPSetTest#getUpperLimit()
	 */
	protected long getUpperLimit() {
		return 1L << 31;
	}
	
	public void testGetLast() throws IOException {
		final MSBDiskFPSet msbDiskFPSet = getMSBDiskFPSet();
		
		// Add the largest possible fingerprint into the fpset. It will end up
		// in the largest bucket. Check that the MSB iterator returns it.
		final long highFP = 1L << 62;
		msbDiskFPSet.put(highFP);
		TLCIterator tlcIterator = new MSBDiskFPSet.TLCIterator(msbDiskFPSet.tbl);
		assertEquals(highFP, tlcIterator.getLast());
		
		// Flush the set to disk (simulating e.g. a checkpoint), a new iterator
		// won't find the element anymore because it intentionally only searches
		// for elements that are *not* on disk.
		msbDiskFPSet.flusher.flushTable();
		new MSBDiskFPSet.TLCIterator(msbDiskFPSet.tbl);
		try {
			tlcIterator.getLast();
		} catch (NoSuchElementException e) {
			// This exception is expected.
			
			// Now add the smallest possible element into the set. It will end
			// up in the smallest bucket.
			final long lowFP = 1;
			msbDiskFPSet.put(lowFP);
			// check that the iterator finds it as the last element.
			tlcIterator = new MSBDiskFPSet.TLCIterator(msbDiskFPSet.tbl);
			assertEquals(lowFP, tlcIterator.getLast());
			return;
		}
		fail();
	}

	/*
	 * Try to get the last element with no elements in the set.
	 */
	public void testGetLastNoBuckets() throws IOException {
		final MSBDiskFPSet msbDiskFPSet = getMSBDiskFPSet();
		

		TLCIterator tlcIterator = new MSBDiskFPSet.TLCIterator(msbDiskFPSet.tbl);
		try {
			tlcIterator.getLast();
		} catch (NoSuchElementException e) {
			return;
		}
		fail();
	}

	private MSBDiskFPSet getMSBDiskFPSet() throws RemoteException, IOException {
		// Create an MSBDiskFPSet usable in this unit test with memory allocated
		// to store 100 fingerprints.
		final DummyFPSetConfiguration fpSetConfig = new DummyFPSetConfiguration();
		fpSetConfig.setMemoryInFingerprintCnt(100);
		assertEquals(100, fpSetConfig.getMemoryInFingerprintCnt());
		
		final String filename = getClass().getName() + System.currentTimeMillis();

		final MSBDiskFPSet msbDiskFPSet = (MSBDiskFPSet) getDiskFPSet(fpSetConfig);
		msbDiskFPSet.init(1, System.getProperty("java.io.tmpdir"), filename);
		return msbDiskFPSet;
	}
}
