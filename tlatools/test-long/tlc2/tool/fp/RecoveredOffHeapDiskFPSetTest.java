// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import java.io.File;
import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Random;

import util.TLCRuntime;

public class RecoveredOffHeapDiskFPSetTest extends AbstractFPSetTest {

	private static final String javaUserDir = System.getProperty(RecoveredOffHeapDiskFPSetTest.class.getName() + ".chkpt",
			System.getProperty("user.home"));
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSet(long)
	 */
	@Override
	protected FPSet getFPSet(long freeMemoryInBytes) throws IOException {
		long freeMemoryInFPs = TLCRuntime.getInstance().getNonHeapPhysicalMemory() / (long) FPSet.LongSize;
		return new OffHeapDiskFPSet(freeMemoryInFPs);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.AbstractFPSetTest#getFPSetInitialized(int)
	 */
	@Override
	protected FPSet getFPSetInitialized(int numThreads) throws IOException {
		final DiskFPSet set = (DiskFPSet) super.getFPSetInitialized(numThreads);
		
		// Create a new FPSet and recover the .fp file that has been generated
		// by the same Java random (seed). This implies, that contains() should
		// return true for all fingerprints in the set. Ideally, we would know
		// the number of fingerprints in .fp.
		
		final String fname = "TestFPSet";
		
		// Create symbolic link to (archived) .chkpt file. One has to create a
		// chkpt file manually by e.g. running testMaxFPSetSizeRnd once. It is
		// important that the chkpt file and this test use the same seed for the
		// RNG though.
		//TODO automagically create the chkpt file or upload to some cloud storage
		final Path link = FileSystems.getDefault().getPath(tmpdir + File.separator + fname + ".fp.chkpt");
		final Path target = FileSystems.getDefault().getPath(javaUserDir + File.separator + fname + ".fp.chkpt");
		Files.createSymbolicLink(link, target);
		
		// diskfpset prepends .fp.chkpt
		set.recover(fname);
		
		return set;
	}
	
	/**
	 * Test is all fingerprints are duplicates. This is the case if the .chkpt file has been created with the same seed.
	 */
	public void testAllDuplicates() throws IOException {
		final Random rnd = new Random(RNG_SEED);
		final FPSet fpSet = getFPSetInitialized();
		
		// FPSet has to contain fpset.size fingerprints
		for (int i = 0; i < fpSet.size(); i++) {
			long fp = rnd.nextLong();
			assertTrue(fpSet.contains(fp));
		}
		
		// The remaining fps coming out of the RNG must not be in fpset. We
		// limit it to 10.000 though.
		for (int i = 0; i < 10000; i++) {
			long fp = rnd.nextLong();
			assertFalse(fpSet.contains(fp));
		}
	}
}
